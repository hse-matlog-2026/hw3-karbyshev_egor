# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/syntax.py

"""Syntactic handling of propositional formulas."""

from __future__ import annotations
from functools import lru_cache
from typing import Mapping, Optional, Set, Tuple, Union

from logic_utils import frozen, memoized_parameterless_method

@lru_cache(maxsize=100)
def is_variable(string: str) -> bool:
    return string[0] >= 'p' and string[0] <= 'z' and \
           (len(string) == 1 or string[1:].isdecimal())

@lru_cache(maxsize=100)
def is_constant(string: str) -> bool:
    return string == 'T' or string == 'F'

@lru_cache(maxsize=100)
def is_unary(string: str) -> bool:
    return string == '~'

@lru_cache(maxsize=100)
def is_binary(string: str) -> bool:
    return string in {'&', '|', '->', '+', '<->', '-&', '-|'}

@frozen
class Formula:
    root: str
    first: Optional[Formula]
    second: Optional[Formula]

    def __init__(self, root: str, first: Optional[Formula] = None,
                 second: Optional[Formula] = None):
        if is_variable(root) or is_constant(root):
            assert first is None and second is None
            self.root = root
        elif is_unary(root):
            assert first is not None and second is None
            self.root, self.first = root, first
        else:
            assert is_binary(root)
            assert first is not None and second is not None
            self.root, self.first, self.second = root, first, second

    @memoized_parameterless_method
    def __repr__(self) -> str:
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        if is_unary(self.root):
            return self.root + str(self.first)
        assert is_binary(self.root)
        return '(' + str(self.first) + self.root + str(self.second) + ')'

    def __eq__(self, other: object) -> bool:
        return isinstance(other, Formula) and str(self) == str(other)

    def __ne__(self, other: object) -> bool:
        return not self == other

    def __hash__(self) -> int:
        return hash(str(self))

    @memoized_parameterless_method
    def variables(self) -> Set[str]:
        if is_variable(self.root):
            return {self.root}
        if is_constant(self.root):
            return set()
        if is_unary(self.root):
            return self.first.variables()
        assert is_binary(self.root)
        return self.first.variables().union(self.second.variables())

    @memoized_parameterless_method
    def operators(self) -> Set[str]:
        if is_variable(self.root):
            return set()
        if is_constant(self.root):
            return {self.root}
        if is_unary(self.root):
            return {self.root}.union(self.first.operators())
        assert is_binary(self.root)
        return {self.root}.union(self.first.operators(),
                                 self.second.operators())
        
    @staticmethod
    def _parse_prefix(string: str) -> Tuple[Union[Formula, None], str]:
        if len(string) == 0:
            return None, 'Unexpected end of input'

        if is_constant(string[0]):
            return Formula(string[0]), string[1:]

        if string[0] >= 'p' and string[0] <= 'z':
            index = 1
            while index < len(string) and string[index].isdecimal():
                index += 1
            variable = string[:index]
            if is_variable(variable):
                return Formula(variable), string[index:]

        if is_unary(string[0]):
            formula, remainder = Formula._parse_prefix(string[1:])
            if formula is None:
                return None, remainder
            return Formula(string[0], formula), remainder

        if string[0] == '(':
            first, remainder = Formula._parse_prefix(string[1:])
            if first is None:
                return None, remainder
            if remainder == '':
                return None, 'Expected binary operator'

            operator = None
            max_op_length = min(3, len(remainder))
            for length in range(max_op_length, 0, -1):
                candidate = remainder[:length]
                if is_binary(candidate):
                    operator = candidate
                    remainder = remainder[length:]
                    break
            if operator is None:
                return None, 'Expected binary operator'

            second, remainder = Formula._parse_prefix(remainder)
            if second is None:
                return None, remainder
            if remainder == '' or remainder[0] != ')':
                return None, 'Expected closing parenthesis'
            return Formula(operator, first, second), remainder[1:]

        return None, 'Invalid formula'

    @staticmethod
    def is_formula(string: str) -> bool:
        formula, remainder = Formula._parse_prefix(string)
        return formula is not None and remainder == ''
        
    @staticmethod
    def parse(string: str) -> Formula:
        assert Formula.is_formula(string)
        formula, remainder = Formula._parse_prefix(string)
        assert formula is not None and remainder == ''
        return formula

    def polish(self) -> str:
        if is_variable(self.root) or is_constant(self.root):
            return self.root
        if is_unary(self.root):
            return self.root + self.first.polish()
        assert is_binary(self.root)
        return self.root + self.first.polish() + self.second.polish()

    @staticmethod
    def parse_polish(string: str) -> Formula:
        def parse_prefix(s: str) -> Tuple[Union[Formula, None], str]:
            if s == '':
                return None, 'Unexpected end of input'

            if is_constant(s[0]):
                return Formula(s[0]), s[1:]

            if s[0] >= 'p' and s[0] <= 'z':
                index = 1
                while index < len(s) and s[index].isdecimal():
                    index += 1
                name = s[:index]
                if is_variable(name):
                    return Formula(name), s[index:]

            if is_unary(s[0]):
                formula, remainder = parse_prefix(s[1:])
                if formula is None:
                    return None, remainder
                return Formula(s[0], formula), remainder

            operator = None
            if len(s) >= 2 and is_binary(s[:2]):
                operator = s[:2]
                remainder = s[2:]
            elif is_binary(s[0]):
                operator = s[0]
                remainder = s[1:]
            else:
                return None, 'Invalid formula'

            first, remainder = parse_prefix(remainder)
            if first is None:
                return None, remainder
            second, remainder = parse_prefix(remainder)
            if second is None:
                return None, remainder
            return Formula(operator, first, second), remainder

        formula, remainder = parse_prefix(string)
        assert formula is not None and remainder == ''
        return formula

    def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> Formula:
        for variable in substitution_map:
            assert is_variable(variable)
        if is_variable(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
            return Formula(self.root)
        if is_constant(self.root):
            return Formula(self.root)
        if is_unary(self.root):
            return Formula(self.root, self.first.substitute_variables(substitution_map))
        if is_binary(self.root):
            return Formula(self.root,
                          self.first.substitute_variables(substitution_map),
                          self.second.substitute_variables(substitution_map))

    def substitute_operators(self, substitution_map: Mapping[str, Formula]) -> Formula:
        for operator in substitution_map:
            assert is_constant(operator) or is_unary(operator) or is_binary(operator)
            assert substitution_map[operator].variables().issubset({'p', 'q'})
        if is_constant(self.root):
            if self.root in substitution_map:
                return substitution_map[self.root]
            return Formula(self.root)
        if is_variable(self.root):
            return Formula(self.root)
        if is_unary(self.root):
            if self.root in substitution_map:
                sub = substitution_map[self.root]
                new_first = self.first.substitute_operators(substitution_map)
                return sub.substitute_variables({'p': new_first})
            return Formula(self.root, self.first.substitute_operators(substitution_map))
        if is_binary(self.root):
            if self.root in substitution_map:
                sub = substitution_map[self.root]
                new_first = self.first.substitute_operators(substitution_map)
                new_second = self.second.substitute_operators(substitution_map)
                return sub.substitute_variables({'p': new_first, 'q': new_second})
            return Formula(self.root,
                          self.first.substitute_operators(substitution_map),
                          self.second.substitute_operators(substitution_map))