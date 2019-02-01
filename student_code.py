# -*-coding:utf-8-*-
import read, copy
from util import *
from logical_classes import *

verbose = 0

class KnowledgeBase(object):
    def __init__(self, facts=[], rules=[]):
        self.facts = facts
        self.rules = rules
        self.ie = InferenceEngine()

    def __repr__(self):
        return 'KnowledgeBase({!r}, {!r})'.format(self.facts, self.rules)

    def __str__(self):
        string = "Knowledge Base: \n"
        string += "\n".join((str(fact) for fact in self.facts)) + "\n"
        string += "\n".join((str(rule) for rule in self.rules))
        return string

    def _get_fact(self, fact):
        """INTERNAL USE ONLY
        Get the fact in the KB that is the same as the fact argument

        Args:
            fact (Fact): Fact we're searching for

        Returns:
            Fact: matching fact
        """
        for kbfact in self.facts:
            if fact == kbfact:
                return kbfact

    def _get_rule(self, rule):
        """INTERNAL USE ONLY
        Get the rule in the KB that is the same as the rule argument

        Args:
            rule (Rule): Rule we're searching for

        Returns:
            Rule: matching rule
        """
        for kbrule in self.rules:
            if rule == kbrule:
                return kbrule

    def kb_add(self, fact_rule):
        """Add a fact or rule to the KB
        Args:
            fact_rule (Fact|Rule) - the fact or rule to be added
        Returns:
            None
        """
        printv("Adding {!r}", 1, verbose, [fact_rule])
        if isinstance(fact_rule, Fact):
            if fact_rule not in self.facts:
                self.facts.append(fact_rule)
                for rule in self.rules:
                    self.ie.fc_infer(fact_rule, rule, self)
            else:
                # update facts or rules' supported by info, sometimes a fact or rule may
                # have been inserted, but when doing re-insert, it's supported by info may
                # change
                if fact_rule.supported_by:
                    ind = self.facts.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.facts[ind].supported_by.append(f)
                else:
                    # label asserted rule or infered rule
                    ind = self.facts.index(fact_rule)
                    self.facts[ind].asserted = True
        elif isinstance(fact_rule, Rule):
            if fact_rule not in self.rules:
                self.rules.append(fact_rule)
                for fact in self.facts:
                    self.ie.fc_infer(fact, fact_rule, self)
            else:
                if fact_rule.supported_by:
                    ind = self.rules.index(fact_rule)
                    for f in fact_rule.supported_by:
                        self.rules[ind].supported_by.append(f)
                else:
                    ind = self.rules.index(fact_rule)
                    self.rules[ind].asserted = True

    def kb_assert(self, fact_rule):
        """Assert a fact or rule into the KB

        Args:
            fact_rule (Fact or Rule): Fact or Rule we're asserting
        """
        printv("Asserting {!r}", 0, verbose, [fact_rule])
        self.kb_add(fact_rule)

    def kb_ask(self, fact):
        """Ask if a fact is in the KB

        Args:
            fact (Fact) - Statement to be asked (will be converted into a Fact)

        Returns:
            listof Bindings|False - list of Bindings if result found, False otherwise
        """
        print("Asking {!r}".format(fact))
        if factq(fact):
            f = Fact(fact.statement)
            bindings_lst = ListOfBindings()
            # ask matched facts
            for fact in self.facts:
                binding = match(f.statement, fact.statement)
                if binding:
                    bindings_lst.add_bindings(binding, [fact])

            return bindings_lst if bindings_lst.list_of_bindings else []

        else:
            print("Invalid ask:", fact.statement)
            return []

    def kb_retract(self, fact_or_rule):
        """Retract a fact from the KB

        Args:
            fact (Fact) - Fact to be retracted

        Returns:
            None
        """
        printv("Retracting {!r}", 0, verbose, [fact_or_rule])
        ####################################################
        # Student code goes here
        # Only fact can be removed
        if isinstance(fact_or_rule, Fact):
            if fact_or_rule not in self.facts:
                print("Fact does not exist")
            else:
                self.retract_helper(fact_or_rule)
        else:
            print("Can not retract rules")

    def retract_helper(self, fact_or_rule, parent=None):
        if isinstance(fact_or_rule, Fact):
            # print("This is a fact")
            if fact_or_rule not in self.facts:
                print("Not existed")
                return
            print(fact_or_rule.statement)
            current = self.facts[self.facts.index(fact_or_rule)]
            if current.asserted and current.supported_by:
                print("Asserted and supported_by not empty cannot be retracted")
                return

            # if supported_by < 2, there must no pair rule and fact can generate this fact, can be deleted
            if len(current.supported_by) < 2:
                self.facts.remove(current)

        # retract rules
        elif isinstance(fact_or_rule, Rule):
            if fact_or_rule not in self.rules:
                print("Not existed")
                return
            print(fact_or_rule.rhs)
            current = self.rules[self.rules.index(fact_or_rule)]
            if (len(current.supported_by) < 2) and (not current.asserted):
                self.rules.remove(current)

            # self.retract_rule_helper(fact_or_rule, parent)
        else:
            print("type === " + str(type(fact_or_rule)))
            print("Something wired happen")
        del_list = []

        # f1 + r1 -> f3
        # f2 + r2 -> f3

        # We have retracted f1, we need to retract f1.supports_by(namely, f3)
        # but f3 cannot be retracted since there is f2 + r2 -> f3
        # In this case, we need to retract f3.supported_by(namely, f1 and r1)
        # retract supports_facts' supported by



        # f = f3
        for f in current.supports_facts:
            res = self.check_delete(f, current)
            if res:
                del_list.extend(res)


        # f1 + r4 -> r5
        # current = f1/r4
        # f = r5
        for f in current.supports_rules:
            res = self.check_delete(f, current)
            if res:
                del_list.extend(res)

        for i in del_list:
            self.retract_helper(i)


    def check_delete(self, child, parent):
        """
        :param child: one of parent's supports fact or rule
        :param parent: fact or rule which is asserted to be deleted
        :return:
        """
        if isinstance(child, Fact):
            child = self.facts[self.facts.index(child)]
        elif isinstance(child, Rule):
            child = self.rules[self.rules.index(child)]
        else:
            print("Something wired happen with child")


        if parent in child.supported_by:
            child.supported_by.remove(parent)
        if len(child.supported_by) >= 3:
            # current fact or rule cannot be deleted,
            # but we need to update it's supported by
            if isinstance(parent, Fact):
                # i = r1, r2
                for i in child.supported_by:
                    if isinstance(i, Rule):
                        binding = match(parent.statement, i.lhs[0])
                        if binding:
                            if instantiate(i.rhs, binding) == child.statement:
                                child.supported_by.remove(i)

            # current = r1
            elif isinstance(parent, Rule):
                # i = f1, f2
                for i in child.supported_by:
                    if isinstance(i, Fact):
                        binding = match(parent.lhs[0], i.statement)
                        if binding:
                            if instantiate(parent.rhs, binding) == child.statement:
                                child.supported_by.remove(i)

            # there is nothing more to delete, so just return an empty list
            return []

        elif len(child.supported_by) <= 1:
            del_list = []
            del_list.append(child)
            # currently this child has been confirmed can be deleted
            # what we need to do is check child's supports_fact or supports_rule
            # whether can be deleted, if can, return it

            for i in child.supports_facts:
                del_list.extend(self.check_delete(i, child))

            for i in child.supports_rules:
                del_list.extend(self.check_delete(i, child))

            return del_list




class InferenceEngine(object):
    def fc_infer(self, fact, rule, kb):
        """Forward-chaining to infer new facts and rules

        Args:
            fact (Fact) - A fact from the KnowledgeBase
            rule (Rule) - A rule from the KnowledgeBase
            kb (KnowledgeBase) - A KnowledgeBase

        Returns:
            Nothing
        """
        printv('Attempting to infer from {!r} and {!r} => {!r}', 1, verbose,
            [fact.statement, rule.lhs, rule.rhs])
        ####################################################
        # Student code goes here
        # When doing inserting, asserted will be automatically set
        binding = match(fact.statement, rule.lhs[0])
        if binding:
            if len(rule.lhs) == 1:
                # insert facts

                statement = instantiate(rule.rhs, binding)
                new_fact = Fact(statement, [fact, rule])

                # update supports_facts
                fact.supports_facts.append(new_fact)
                rule.supports_facts.append(new_fact)

                kb.kb_assert(new_fact)
            else:
                # insert rules
                lhs = []

                for i in range(1, len(rule.lhs)):
                    lhs.append(instantiate(rule.lhs[i], binding))
                rhs = instantiate(rule.rhs, binding)
                rules = []
                rules.append(lhs)
                rules.append(rhs)
                new_rule = Rule(rules, [fact, rule])

                fact.supports_rules.append(new_rule)
                rule.supports_rules.append(new_rule)

                kb.kb_assert(new_rule)
