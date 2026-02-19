# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2022
# File name: propositions/operators.py

"""Syntactic conversion of propositional formulas to use only specific sets of
operators."""

from propositions.syntax import *
from propositions.semantics import *

def to_not_and_or(formula: Formula) -> Formula:
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('|', Formula('p'), Formula('~', Formula('p')))
        else:
            return Formula('&', Formula('p'), Formula('~', Formula('p')))
    if is_variable(formula.root):
        return Formula(formula.root)
    if is_unary(formula.root):
        return Formula('~', to_not_and_or(formula.first))
    if is_binary(formula.root):
        first = to_not_and_or(formula.first)
        second = to_not_and_or(formula.second)
        if formula.root == '&':
            return Formula('&', first, second)
        if formula.root == '|':
            return Formula('|', first, second)
        if formula.root == '->':
            return Formula('|', Formula('~', first), second)
        if formula.root == '+':
            return Formula('|',
                          Formula('&', first, Formula('~', second)),
                          Formula('&', Formula('~', first), second))
        if formula.root == '<->':
            return Formula('|',
                          Formula('&', first, second),
                          Formula('&', Formula('~', first), Formula('~', second)))
        if formula.root == '-&':
            return Formula('~', Formula('&', first, second))
        if formula.root == '-|':
            return Formula('~', Formula('|', first, second))

def to_not_and(formula: Formula) -> Formula:
    not_and_or = to_not_and_or(formula)
    if is_constant(not_and_or.root):
        return not_and_or
    if is_variable(not_and_or.root):
        return not_and_or
    if is_unary(not_and_or.root):
        return Formula('~', to_not_and(not_and_or.first))
    if not_and_or.root == '&':
        return Formula('&', to_not_and(not_and_or.first),
                      to_not_and(not_and_or.second))
    if not_and_or.root == '|':
        return Formula('~',
                      Formula('&',
                             Formula('~', to_not_and(not_and_or.first)),
                             Formula('~', to_not_and(not_and_or.second))))

def to_nand(formula: Formula) -> Formula:
    not_and = to_not_and(formula)
    if is_variable(not_and.root):
        return not_and
    if is_unary(not_and.root):
        arg = to_nand(not_and.first)
        return Formula('-&', arg, arg)
    if not_and.root == '&':
        left = to_nand(not_and.first)
        right = to_nand(not_and.second)
        nand = Formula('-&', left, right)
        return Formula('-&', nand, nand)

def to_implies_not(formula: Formula) -> Formula:
    if is_variable(formula.root):
        return formula
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('p'), Formula('p'))
        else:
            return Formula('~', Formula('->', Formula('p'), Formula('p')))
    new_first = to_implies_not(formula.first)
    new_second = to_implies_not(formula.second) if formula.second else None
    if formula.root == '~':
        return Formula('~', new_first)
    if formula.root == '->':
        return Formula('->', new_first, new_second)
    if formula.root == '&':
        return Formula('~', Formula('->', new_first, Formula('~', new_second)))
    if formula.root == '|':
        return Formula('->', Formula('~', new_first), new_second)
    if formula.root == '+':
        left = Formula('->', new_first, Formula('~', new_second))
        right = Formula('->', Formula('~', new_first), new_second)
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '<->':
        left = Formula('->', new_first, new_second)
        right = Formula('->', new_second, new_first)
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '-&':
        return Formula('->', new_first, Formula('~', new_second))
    if formula.root == '-|':
        return Formula('~', Formula('->', Formula('~', new_first), new_second))

def to_implies_false(formula: Formula) -> Formula:
    imp_not = to_implies_not(formula)
    if is_variable(imp_not.root):
        return imp_not
    if imp_not.root == 'F':
        return imp_not
    if imp_not.root == '~':
        return Formula('->', to_implies_false(imp_not.first), Formula('F'))
    if imp_not.root == '->':
        return Formula('->', to_implies_false(imp_not.first), to_implies_false(imp_not.second))