# Copyright 2012 Locaweb.
# All Rights Reserved.
#
#    Licensed under the Apache License, Version 2.0 (the "License");
#    you may not use this file except in compliance with the License.
#    You may obtain a copy of the License at
#
#        http://www.apache.org/licenses/LICENSE-2.0
#
#    Unless required by applicable law or agreed to in writing, software
#    distributed under the License is distributed on an "AS IS" BASIS,
#    WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
#    See the License for the specific language governing permissions and
#    limitations under the License.
#
# based on
# https://github.com/openstack/nova/blob/master/nova/network/linux_net.py

"""Implements iptables rules using linux utilities."""

import collections
import contextlib
import os
import re
import sys
import signal
import pickle

from oslo_concurrency import lockutils
from oslo_config import cfg
from oslo_log import log as logging
from oslo_utils import excutils

from eventlet.green import subprocess
from eventlet import greenthread

from trove.common.exception import IpTablesApplyException 
from trove.common.i18n import _LE, _LW, _ 

LOG = logging.getLogger(__name__)

"""
def logm(*message):
    print(message)
    print('\n')
LOG.debug = logm
LOG.error = logm
LOG.exception = logm
LOG.warn = logm
"""

SYNCHRONIZED_PREFIX = 'trove-'	

"""iptables comments"""
SNAT_OUT = 'Perform source NAT on outgoing traffic.'
UNMATCH_DROP = 'Default drop rule for unmatched traffic.'
VM_INT_SG = 'Direct traffic from the VM interface to the security group chain.'
SG_TO_VM_SG = 'Jump to the VM specific chain.'
INPUT_TO_SG = 'Direct incoming traffic from VM to the security group chain.'
PAIR_ALLOW = 'Allow traffic from defined IP/MAC pairs.'
PAIR_DROP = 'Drop traffic without an IP/MAC allow rule.'
DHCP_CLIENT = 'Allow DHCP client traffic.'
DHCP_SPOOF = 'Prevent DHCP Spoofing by VM.'
UNMATCHED = 'Send unmatched traffic to the fallback chain.'
INVALID_DROP = ("Drop packets that appear related to an existing connection "
		                "(e.g. TCP ACK/FIN) but do not have an entry in conntrack.")
ALLOW_ASSOC = ('Direct packets associated with a known session to the RETURN '
		               'chain.')
IPV6_RA_ALLOW = 'Allow IPv6 ICMP traffic to allow RA packets.'
PORT_SEC_ACCEPT = 'Accept all packets when port security is disabled.'

data_persistence_path = "/export/iptables-rule.dp"

# NOTE(vish): Iptables supports chain names of up to 28 characters,  and we
#             add up to 12 characters to binary_name which is used as a prefix,
#             so we limit it to 16 characters.
#             (max_chain_name_length - len('-POSTROUTING') == 16)
def get_binary_name():
    """Grab the name of the binary we're running in."""
    return os.path.basename(sys.argv[0])[:16].replace(' ', '_')

binary_name = get_binary_name()

# A length of a chain name must be less than or equal to 11 characters.
# <max length of iptables chain name> - (<binary_name> + '-') = 28-(16+1) = 11
MAX_CHAIN_LEN_WRAP = 11
MAX_CHAIN_LEN_NOWRAP = 28

# Number of iptables rules to print before and after a rule that causes a
# a failure during iptables-restore
IPTABLES_ERROR_LINES_OF_CONTEXT = 5

#porting from neutron/agent/linux/utils.piy

def _subprocess_setup():
	    # Python installs a SIGPIPE handler by default. This is usually not what
	    # non-Python subprocesses expect.
	    signal.signal(signal.SIGPIPE, signal.SIG_DFL)


def subprocess_popen(args, stdin=None, stdout=None, stderr=None, shell=False,
		             env=None, preexec_fn=_subprocess_setup, close_fds=True):

	return subprocess.Popen(args, shell=shell, stdin=stdin, stdout=stdout,
	     	                stderr=stderr, preexec_fn=preexec_fn,
							close_fds=close_fds, env=env)

def addl_env_args(addl_env):
    """Build arugments for adding additional environment vars with env"""

    # NOTE (twilson) If using rootwrap, an EnvFilter should be set up for the
    # command instead of a CommandFilter.
    if addl_env is None:
        return []
    return ['env'] + ['%s=%s' % pair for pair in addl_env.items()]


def create_process(cmd, run_as_root=False, addl_env=None):
    """Create a process object for the given command.

    The return value will be a tuple of the process object and the
    list of command arguments used to create it.
    """
    cmd = map(str, addl_env_args(addl_env) + cmd)
    if run_as_root:
        cmd = ['sudo'] + cmd
    LOG.debug("Running command: %s", cmd)
    obj = subprocess_popen(cmd, shell=False,
                                 stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE,
                                 stderr=subprocess.PIPE)

    return obj, cmd

def execute(cmd, process_input=None, addl_env=None,
            check_exit_code=True, return_stderr=False, log_fail_as_error=True,
            extra_ok_codes=None, run_as_root=False):
    try:
        obj, cmd = create_process(cmd, run_as_root=run_as_root,
                                  addl_env=addl_env)
        _stdout, _stderr = obj.communicate(process_input)
        returncode = obj.returncode
        obj.stdin.close()

        m = _("\nCommand: {cmd}\nExit code: {code}\nStdin: {stdin}\n"
              "Stdout: {stdout}\nStderr: {stderr}").format(
                  cmd=cmd,
                  code=returncode,
                  stdin=process_input or '',
                  stdout=_stdout,
                  stderr=_stderr)

        extra_ok_codes = extra_ok_codes or []
        if returncode and returncode in extra_ok_codes:
            returncode = None

        if returncode and log_fail_as_error:
            LOG.error(m)
        else:
            LOG.debug(m)

        if returncode and check_exit_code:
            raise RuntimeError(m)
    finally:
        # NOTE(termie): this appears to be necessary to let the subprocess
        #               call clean something up in between calls, without
        #               it two execute calls in a row hangs the second one
        greenthread.sleep(0)

    return (_stdout, _stderr) if return_stderr else _stdout

def comment_rule(rule, comment):
    #if not cfg.CONF.AGENT.comment_iptables_rules or not comment:
    if not comment:
        return rule
    # iptables-save outputs the comment before the jump so we need to match
    # that order so _find_last_entry works
    comment = '-m comment --comment "%s"' % comment
    if rule.startswith('-j'):
        # this is a jump only rule so we just put the comment first
        return '%s %s' % (comment, rule)
    try:
        jpos = rule.index(' -j ')
        return ' '.join((rule[:jpos], comment, rule[jpos + 1:]))
    except ValueError:
        return '%s %s' % (rule, comment)


def get_chain_name(chain_name, wrap=True):
    if wrap:
        return chain_name[:MAX_CHAIN_LEN_WRAP]
    else:
        return chain_name[:MAX_CHAIN_LEN_NOWRAP]


class IptablesRule(object):
    """An iptables rule.

    You shouldn't need to use this class directly, it's only used by
    IptablesManager.

    """

    def __init__(self, chain, rule, wrap=True, top=False,
                 binary_name=binary_name, tag=None, comment=None):
        self.chain = get_chain_name(chain, wrap)
        self.rule = rule
        self.wrap = wrap
        self.top = top
        self.wrap_name = binary_name[:16]
        self.tag = tag
        self.comment = comment

    def __eq__(self, other):
        return ((self.chain == other.chain) and
                (self.rule == other.rule) and
                (self.top == other.top) and
                (self.wrap == other.wrap))

    def __ne__(self, other):
        return not self == other

    def __str__(self):
        if self.wrap:
            chain = '%s-%s' % (self.wrap_name, self.chain)
        else:
            chain = self.chain
        return comment_rule('-A %s %s' % (chain, self.rule), self.comment)


class IptablesTable(object):
    """An iptables table."""

    def __init__(self, binary_name=binary_name):
        self.rules = []
        self.remove_rules = []
        self.chains = set()
        self.unwrapped_chains = set()
        self.remove_chains = set()
        self.wrap_name = binary_name[:16]

    def add_chain(self, name, wrap=True):
        """Adds a named chain to the table.

        The chain name is wrapped to be unique for the component creating
        it, so different components of Nova can safely create identically
        named chains without interfering with one another.

        At the moment, its wrapped name is <binary name>-<chain name>,
        so if neutron-openvswitch-agent creates a chain named 'OUTPUT',
        it'll actually end up being named 'neutron-openvswi-OUTPUT'.

        """
        name = get_chain_name(name, wrap)
        if wrap:
            self.chains.add(name)
        else:
            self.unwrapped_chains.add(name)

    def _select_chain_set(self, wrap):
        if wrap:
            return self.chains
        else:
            return self.unwrapped_chains

    def remove_chain(self, name, wrap=True):
        """Remove named chain.

        This removal "cascades". All rule in the chain are removed, as are
        all rules in other chains that jump to it.

        If the chain is not found, this is merely logged.

        """
        name = get_chain_name(name, wrap)
        chain_set = self._select_chain_set(wrap)

        if name not in chain_set:
            LOG.debug('Attempted to remove chain %s which does not exist',
                      name)
            return

        chain_set.remove(name)

        if not wrap:
            # non-wrapped chains and rules need to be dealt with specially,
            # so we keep a list of them to be iterated over in apply()
            self.remove_chains.add(name)

            # first, add rules to remove that have a matching chain name
            self.remove_rules += [r for r in self.rules if r.chain == name]

        # next, remove rules from list that have a matching chain name
        self.rules = [r for r in self.rules if r.chain != name]

        if not wrap:
            jump_snippet = '-j %s' % name
            # next, add rules to remove that have a matching jump chain
            self.remove_rules += [r for r in self.rules
                                  if jump_snippet in r.rule]
        else:
            jump_snippet = '-j %s-%s' % (self.wrap_name, name)

        # finally, remove rules from list that have a matching jump chain
        self.rules = [r for r in self.rules
                      if jump_snippet not in r.rule]

    def add_rule(self, chain, rule, wrap=True, top=False, tag=None,
                 comment=None):
        """Add a rule to the table.

        This is just like what you'd feed to iptables, just without
        the '-A <chain name>' bit at the start.

        However, if you need to jump to one of your wrapped chains,
        prepend its name with a '$' which will ensure the wrapping
        is applied correctly.

        """
        chain = get_chain_name(chain, wrap)
        if wrap and chain not in self.chains:
            raise LookupError(_('Unknown chain: %r') % chain)

        if '$' in rule:
            rule = ' '.join(
                self._wrap_target_chain(e, wrap) for e in rule.split(' '))

        self.rules.append(IptablesRule(chain, rule, wrap, top, self.wrap_name,
                                       tag, comment))

    def _wrap_target_chain(self, s, wrap):
        if s.startswith('$'):
            s = ('%s-%s' % (self.wrap_name, get_chain_name(s[1:], wrap)))

        return s

    def remove_rule(self, chain, rule, wrap=True, top=False, comment=None):
        """Remove a rule from a chain.

        Note: The rule must be exactly identical to the one that was added.
        You cannot switch arguments around like you can with the iptables
        CLI tool.

        """
        chain = get_chain_name(chain, wrap)
        try:
            if '$' in rule:
                rule = ' '.join(
                    self._wrap_target_chain(e, wrap) for e in rule.split(' '))

            self.rules.remove(IptablesRule(chain, rule, wrap, top,
                                           self.wrap_name,
                                           comment=comment))
            if not wrap:
                self.remove_rules.append(IptablesRule(chain, rule, wrap, top,
                                                      self.wrap_name,
                                                      comment=comment))
        except ValueError:
            LOG.warn(_LW('Tried to remove rule that was not there:'
                         ' %(chain)r %(rule)r %(wrap)r %(top)r'),
                     {'chain': chain, 'rule': rule,
                      'top': top, 'wrap': wrap})

    def _get_chain_rules(self, chain, wrap):
        chain = get_chain_name(chain, wrap)
        return [rule for rule in self.rules
                if rule.chain == chain and rule.wrap == wrap]

    def empty_chain(self, chain, wrap=True):
        """Remove all rules from a chain."""
        chained_rules = self._get_chain_rules(chain, wrap)
        for rule in chained_rules:
            self.rules.remove(rule)

    def clear_rules_by_tag(self, tag):
        if not tag:
            return
        rules = [rule for rule in self.rules if rule.tag == tag]
        for rule in rules:
            self.rules.remove(rule)


class IptablesManager(object):
    """Wrapper for iptables.

    See IptablesTable for some usage docs

    A number of chains are set up to begin with.

    First, neutron-filter-top. It's added at the top of FORWARD and OUTPUT.
    Its name is not wrapped, so it's shared between the various neutron
    workers. It's intended for rules that need to live at the top of the
    FORWARD and OUTPUT chains. It's in both the ipv4 and ipv6 set of tables.

    For ipv4 and ipv6, the built-in INPUT, OUTPUT, and FORWARD filter chains
    are wrapped, meaning that the "real" INPUT chain has a rule that jumps to
    the wrapped INPUT chain, etc. Additionally, there's a wrapped chain named
    "local" which is jumped to from neutron-filter-top.

    For ipv4, the built-in PREROUTING, OUTPUT, and POSTROUTING nat chains are
    wrapped in the same was as the built-in filter chains. Additionally,
    there's a snat chain that is applied after the POSTROUTING chain.

    """

    def __init__(self, _execute=None, state_less=False, use_ipv6=False,
                 namespace=None, binary_name=binary_name):
        if _execute:
            self.execute = _execute
        else:
            self.execute = execute

        #//config.register_iptables_opts(cfg.CONF)
        self.use_ipv6 = use_ipv6
        self.namespace = namespace
        self.iptables_apply_deferred = False
        self.wrap_name = binary_name[:16]

        self.ipv4 = {'filter': IptablesTable(binary_name=self.wrap_name)}
        self.ipv6 = {'filter': IptablesTable(binary_name=self.wrap_name)}

        # Add a neutron-filter-top chain. It's intended to be shared
        # among the various neutron components. It sits at the very top
        # of FORWARD and OUTPUT.

        if os.path.isfile("/export/iptables-rule.dp"):
            self.data_reload()
        else:
            for tables in [self.ipv4, self.ipv6]:
                tables['filter'].add_chain('RDS_DIFF_SYSTEM', wrap=False)
                tables['filter'].add_chain('RDS_CO_SYSTEM', wrap=False)
                tables['filter'].add_chain('RDS_USER', wrap=False)

            # Wrap the built-in chains
            builtin_chains = {4: {'filter': ['INPUT', 'OUTPUT', 'FORWARD']},
                              6: {'filter': ['INPUT', 'OUTPUT', 'FORWARD']}}

            #when restart guest agent service, reload data from persistant file.
            tables = self.ipv4
            tables['filter'].add_rule('INPUT', '-j %s' % ('RDS_DIFF_SYSTEM'), wrap=False, top=True)
            tables['filter'].add_rule('INPUT', '-j %s' % ('RDS_CO_SYSTEM'), wrap=False, top=True)
            tables['filter'].add_rule('INPUT', '-j %s' % ('RDS_USER'), wrap=False, top=True)

    def get_chain(self, table, chain, ip_version=4, wrap=True):
        try:
            requested_table = {4: self.ipv4, 6: self.ipv6}[ip_version][table]
        except KeyError:
            return []
        return requested_table._get_chain_rules(chain, wrap)

    def is_chain_empty(self, table, chain, ip_version=4, wrap=True):
        return not self.get_chain(table, chain, ip_version, wrap)

    @contextlib.contextmanager
    def defer_apply(self):
        """Defer apply context."""
        self.defer_apply_on()
        try:
            yield
        finally:
            try:
                self.defer_apply_off()
            except Exception:
                msg = _LE('Failure applying iptables rules')
                LOG.exception(msg)
                raise IpTablesApplyException(msg)

    def defer_apply_on(self):
        self.iptables_apply_deferred = True

    def defer_apply_off(self):
        self.iptables_apply_deferred = False
        self._apply()

    def data_persistence(self):
        #for data persistence
        pickle.dump(self.ipv4['filter'], open(data_persistence_path, "w"))

    def data_reload(self):
        #for data persistence
        if os.path.isfile(data_persistence_path):
            self.ipv4['filter'] = pickle.load(open(data_persistence_path, "r"))

    def apply(self):
        if self.iptables_apply_deferred:
            return
        self._apply()
        self.data_persistence()

    def _apply(self):
        return self._apply_synchronized()

    def _apply_synchronized(self):
        """Apply the current in-memory set of iptables rules.

        This will blow away any rules left over from previous runs of the
        same component of Nova, and replace them with our current set of
        rules. This happens atomically, thanks to iptables-restore.

        """
        s = [('iptables', self.ipv4)]
        if self.use_ipv6:
            s += [('ip6tables', self.ipv6)]

        for cmd, tables in s:
            args = ['%s-save' % (cmd,), '-c']
            if self.namespace:
                args = ['ip', 'netns', 'exec', self.namespace] + args
            all_tables = self.execute(args, run_as_root=True)
            all_lines = all_tables.split('\n')
            # Traverse tables in sorted order for predictable dump output
            for table_name in sorted(tables):
                table = tables[table_name]
                start, end = self._find_table(all_lines, table_name)
                all_lines[start:end] = self._modify_rules(
                    all_lines[start:end], table, table_name)

            args = ['%s-restore' % (cmd,), '-c']
            if self.namespace:
                args = ['ip', 'netns', 'exec', self.namespace] + args
            try:
                self.execute(args, process_input='\n'.join(all_lines),
                             run_as_root=True)
            except RuntimeError as r_error:
                with excutils.save_and_reraise_exception():
                    try:
                        line_no = int(re.search(
                            'iptables-restore: line ([0-9]+?) failed',
                            str(r_error)).group(1))
                        context = IPTABLES_ERROR_LINES_OF_CONTEXT
                        log_start = max(0, line_no - context)
                        log_end = line_no + context
                    except AttributeError:
                        # line error wasn't found, print all lines instead
                        log_start = 0
                        log_end = len(all_lines)
                    log_lines = ('%7d. %s' % (idx, l)
                                 for idx, l in enumerate(
                                     all_lines[log_start:log_end],
                                     log_start + 1)
                                 )
                    LOG.error(_LE("IPTablesManager.apply failed to apply the "
                                  "following set of iptables rules:\n%s"),
                              '\n'.join(log_lines))
        LOG.debug("IPTablesManager.apply completed with success")

    def _find_table(self, lines, table_name):
        if len(lines) < 3:
            # length only <2 when fake iptables
            return (0, 0)
        try:
            start = lines.index('*%s' % table_name) - 1
        except ValueError:
            # Couldn't find table_name
            LOG.debug('Unable to find table %s', table_name)
            return (0, 0)
        end = lines[start:].index('COMMIT') + start + 2
        return (start, end)

    def _find_rules_index(self, lines):
        seen_chains = False
        rules_index = 0
        for rules_index, rule in enumerate(lines):
            if not seen_chains:
                if rule.startswith(':'):
                    seen_chains = True
            else:
                if not rule.startswith(':'):
                    break

        if not seen_chains:
            rules_index = 2

        return rules_index

    def _find_last_entry(self, filter_map, match_str):
        # find last matching entry
        try:
            return filter_map[match_str][-1]
        except KeyError:
            pass

    def _modify_rules(self, current_lines, table, table_name):
        # Chains are stored as sets to avoid duplicates.
        # Sort the output chains here to make their order predictable.
        unwrapped_chains = sorted(table.unwrapped_chains)
        chains = sorted(table.chains)
        remove_chains = table.remove_chains
        rules = table.rules
        remove_rules = table.remove_rules

        if not current_lines:
            fake_table = ['# Generated by iptables_manager',
                          '*' + table_name, 'COMMIT',
                          '# Completed by iptables_manager']
            current_lines = fake_table

        # Fill old_filter with any chains or rules we might have added,
        # they could have a [packet:byte] count we want to preserve.
        # Fill new_filter with any chains or rules without our name in them.
        old_filter, new_filter = [], []
        for line in current_lines:
            (old_filter if self.wrap_name in line else
             new_filter).append(line.strip())

        old_filter_map = make_filter_map(old_filter)
        new_filter_map = make_filter_map(new_filter)

        rules_index = self._find_rules_index(new_filter)

        all_chains = [':%s' % name for name in unwrapped_chains]
        all_chains += [':%s-%s' % (self.wrap_name, name) for name in chains]

        # Iterate through all the chains, trying to find an existing
        # match.
        our_chains = []
        for chain in all_chains:
            chain_str = str(chain).strip()

            old = self._find_last_entry(old_filter_map, chain_str)
            if not old:
                dup = self._find_last_entry(new_filter_map, chain_str)
            new_filter = [s for s in new_filter if chain_str not in s.strip()]

            # if no old or duplicates, use original chain
            if old or dup:
                chain_str = str(old or dup)
            else:
                # add-on the [packet:bytes]
                chain_str += ' - [0:0]'

            our_chains += [chain_str]

        # Iterate through all the rules, trying to find an existing
        # match.
        our_rules = []
        bot_rules = []
        for rule in rules:
            rule_str = str(rule).strip()
            # Further down, we weed out duplicates from the bottom of the
            # list, so here we remove the dupes ahead of time.

            old = self._find_last_entry(old_filter_map, rule_str)
            if not old:
                dup = self._find_last_entry(new_filter_map, rule_str)
            #new_filter = [s for s in new_filter if rule_str not in s.strip()]

            # if no old or duplicates, use original rule
            if old or dup:
                rule_str = str(old or dup)
                # backup one index so we write the array correctly
                #if not old:
                #    rules_index -= 1
            else:
                # add-on the [packet:bytes]
                rule_str = '[0:0] ' + rule_str

            if rule.top:
                # rule.top == True means we want this rule to be at the top.
                our_rules += [rule_str]
            else:
                bot_rules += [rule_str]

        our_rules += bot_rules

        new_filter[rules_index:rules_index] = our_rules
        new_filter[rules_index:rules_index] = our_chains

        def _strip_packets_bytes(line):
            # strip any [packet:byte] counts at start or end of lines
            if line.startswith(':'):
                # it's a chain, for example, ":neutron-billing - [0:0]"
                line = line.split(':')[1]
                line = line.split(' - [', 1)[0]
            elif line.startswith('['):
                # it's a rule, for example, "[0:0] -A neutron-billing..."
                line = line.split('] ', 1)[1]
            line = line.strip()
            return line

        seen_chains = set()

        def _weed_out_duplicate_chains(line):
            # ignore [packet:byte] counts at end of lines
            if line.startswith(':'):
                line = _strip_packets_bytes(line)
                if line in seen_chains:
                    return False
                else:
                    seen_chains.add(line)

            # Leave it alone
            return True

        seen_rules = set()

        def _weed_out_duplicate_rules(line):
            if line.startswith('['):
                line = _strip_packets_bytes(line)
                if line in seen_rules:
                    return False
                else:
                    seen_rules.add(line)

            # Leave it alone
            return True

        def _weed_out_removes(line):
            # We need to find exact matches here
            if line.startswith(':'):
                line = _strip_packets_bytes(line)
                for chain in remove_chains:
                    if chain == line:
                        remove_chains.remove(chain)
                        return False
            elif line.startswith('['):
                line = _strip_packets_bytes(line)
                for rule in remove_rules:
                    rule_str = _strip_packets_bytes(str(rule))
                    if rule_str == line:
                        remove_rules.remove(rule)
                        return False

            # Leave it alone
            return True

        # We filter duplicates.  Go through the chains and rules, letting
        # the *last* occurrence take precedence since it could have a
        # non-zero [packet:byte] count we want to preserve.  We also filter
        # out anything in the "remove" list.
        new_filter.reverse()
        new_filter = [line for line in new_filter
                      if _weed_out_duplicate_chains(line) and
                      _weed_out_duplicate_rules(line) and
                      _weed_out_removes(line)]
        new_filter.reverse()

        # flush lists, just in case we didn't find something
        remove_chains.clear()
        for rule in remove_rules:
            remove_rules.remove(rule)

        return new_filter

    def _get_traffic_counters_cmd_tables(self, chain, wrap=True):
        name = get_chain_name(chain, wrap)

        cmd_tables = [('iptables', key) for key, table in self.ipv4.items()
                      if name in table._select_chain_set(wrap)]

        if self.use_ipv6:
            cmd_tables += [('ip6tables', key)
                           for key, table in self.ipv6.items()
                           if name in table._select_chain_set(wrap)]

        return cmd_tables

    def get_traffic_counters(self, chain, wrap=True, zero=False):
        """Return the sum of the traffic counters of all rules of a chain."""
        cmd_tables = self._get_traffic_counters_cmd_tables(chain, wrap)
        if not cmd_tables:
            LOG.warn(_LW('Attempted to get traffic counters of chain %s which '
                         'does not exist'), chain)
            return

        name = get_chain_name(chain, wrap)
        acc = {'pkts': 0, 'bytes': 0}

        for cmd, table in cmd_tables:
            args = [cmd, '-t', table, '-L', name, '-n', '-v', '-x']
            if zero:
                args.append('-Z')
            if self.namespace:
                args = ['ip', 'netns', 'exec', self.namespace] + args
            current_table = self.execute(args, run_as_root=True)
            current_lines = current_table.split('\n')

            for line in current_lines[2:]:
                if not line:
                    break
                data = line.split()
                if (len(data) < 2 or
                        not data[0].isdigit() or
                        not data[1].isdigit()):
                    break

                acc['pkts'] += int(data[0])
                acc['bytes'] += int(data[1])

        return acc

    def flush(self):
        args = ['iptables', '-F']
        self.execute(args, run_as_root=True)
        args = ['iptables', '-X']
        self.execute(args, run_as_root=True)

        for tables in [self.ipv4, self.ipv6]:
            tables['filter'].empty_chain('RDS_DIFF_SYSTEM', wrap=False)
            tables['filter'].empty_chain('RDS_CO_SYSTEM', wrap=False)
            tables['filter'].empty_chain('RDS_USER', wrap=False)
        self.data_persistence()
        os.unlink(data_persistence_path)

def make_filter_map(filter_list):
    filter_map = collections.defaultdict(list)
    for data in filter_list:
        # strip any [packet:byte] counts at start or end of lines,
        # for example, chains look like ":neutron-foo - [0:0]"
        # and rules look like "[0:0] -A neutron-foo..."
        if data.startswith('['):
            key = data.rpartition('] ')[2]
        elif data.endswith(']'):
            key = data.rsplit(' [', 1)[0]
            if key.endswith(' -'):
                key = key[:-2]
        else:
            # things like COMMIT, *filter, and *nat land here
            continue
        filter_map[key].append(data)
        # regular IP(v6) entries are translated into /32s or /128s so we
        # include a lookup without the CIDR here to match as well
        for cidr in ('/32', '/128'):
            if cidr in key:
                alt_key = key.replace(cidr, '')
                filter_map[alt_key].append(data)
    # return a regular dict so readers don't accidentally add entries
    return dict(filter_map)

iptables_mgr = IptablesManager(use_ipv6=False,state_less=True)
chain_name_mapper = {
    "sys-diff":"RDS_DIFF_SYSTEM", #ingress
    "sys-com":"RDS_CO_SYSTEM", #ingress
    "user":"RDS_USER", #ingress
    "output":"OUTPUT" #egress
}

def _set_secgroup_rules(set_action,rules):
    """
    set security group rules using iptalbes
    set_action: add/remove
    """
    LOG.debug("_add_secgroup_rules(%s)" % rules)
    for rule in rules:
        protocol = rule['protocol']
        from_port = rule['from_port']
        to_port = rule['to_port']
        cidr = rule['cidr']
        action = rule['action']
        chain = rule['chain']
        
        if chain in ['sys-com','sys-diff', 'user', 'output']:
            """
            ingress rules: -s 192.168.1.0/24 -p tcp -m tcp --dport 1-65536 -j ACCEPT OUTPUT
            egress rules: -d 192.168.1.0/24 -p tcp -m tcp --dport 1-65536 -j ACCEPT OUTPUT
            """
            rule1_str = ''
            if cidr:
                if chain in ['sys-com','sys-diff', 'user']:
                    #ingress rule
                    rule1_str += '-s %s ' % cidr
                else: #output chain
                    #egress rules
                    rule1_str += '-d %s ' % cidr
            if protocol in ['tcp', 'udp', 'igmp']:
                rule1_str += '-p %s -m %s ' % (protocol,protocol)
            if to_port and from_port :
                if int(from_port) < int(to_port):
                    rule1_str += '--dport %s:%s ' % (from_port,to_port)
                elif int(from_port) == int(to_port):
                    rule1_str += '--dport %s ' % (from_port)
            top = False
            if action in ['accept', 'drop']:
                rule1_str += '-j %s ' % action.upper()
                top = True if action == 'accept' else False
            if set_action == "add":
                 iptables_mgr.ipv4['filter'].add_rule(chain_name_mapper[chain], rule1_str, wrap=False, top=top)
            elif set_action == "remove":
                 iptables_mgr.ipv4['filter'].remove_rule(chain_name_mapper[chain], rule1_str, wrap=False, top=top)


def apply_secgroup_rules(rules):
    """
    add security group rules using iptalbes
    """
    iptables_mgr.flush()
    LOG.debug("apply_secgroup_rules(%s)" % rules)
    _set_secgroup_rules('add',rules)   
    iptables_mgr.apply()

def remove_secgroup_rules():
    """
    remove security group rules in docker
    """
    LOG.debug('remove_secgroup_rules')
    iptables_mgr.flush()

def add_secgroup_rules(rules):
    """
    add security group rules using iptalbes
    """
    LOG.debug("add_secgroup_rules(%s)" % rules)
    _set_secgroup_rules('add',rules)
    iptables_mgr.apply()

def delete_secgroup_rules(rules):
    """
    delete security group rules using iptalbes
    """
    LOG.debug("delete_secgroup_rules(%s)" % rules)
    _set_secgroup_rules('remove',rules)
    iptables_mgr.apply()

if __name__ == "__main__":
    #iptables_mgr = IptablesManager(use_ipv6=False,state_less=True)
    rules = [
        {
            'protocol': 'tcp',
            'from_port': '22',
            'to_port': '22',
            'cidr': '',
            'action': 'accept',
            'chain': 'user'
        },
        {
            'protocol': 'tcp',
            'from_port': '3306',
            'to_port': '3306',
            'cidr': '',
            'action': 'accept',
            'chain': 'user'
        },
        {
            'protocol': 'udp',
            'from_port': '3000',
            'to_port': '4000',
            'cidr': '192.177.0.0/16',
            'action': 'accept',
            'chain': 'sys-com'
        },
        {
            'protocol': 'tcp',
            'from_port': '5000',
            'to_port': '5000',
            'cidr': '192.177.1.2/32',
            'action': 'drop',
            'chain': 'sys-com'
        }

    ]
    rules1 = [
        {
            'protocol': 'tcp',
            'from_port': '3306',
            'to_port': '3306',
            'cidr': '',
            'action': 'accept',
            'chain': 'user'
       }
    ]

    rules2 = [
        {
            'protocol': 'tcp',
            'from_port': '3306',
            'to_port': '3306',
            'cidr': '',
            'action': 'accept',
            'chain': 'output'
        },
        {
            'protocol': 'udp',
            'from_port': '3000',
            'to_port': '4000',
            'cidr': '192.178.0.0/16',
            'action': 'accept',
            'chain': 'sys-com'
        },
        {
            'protocol': 'tcp',
            'from_port': '5000',
            'to_port': '5000',
            'cidr': '192.178.1.2/32',
            'action': 'drop',
            'chain': 'output'
        }
    ]
    
    import pdb
    pdb.set_trace()

    apply_secgroup_rules(rules)
    add_secgroup_rules(rules)
    add_secgroup_rules(rules2)
    delete_secgroup_rules(rules)
    remove_secgroup_rules()
