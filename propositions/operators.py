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
        return Formula(formula.root)
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('p'), Formula('p'))
        else:  # 'F'
            return Formula('~', Formula('->', Formula('p'), Formula('p')))
    if formula.root == '~' or formula.root == '->':
        if is_unary(formula.root):
            return Formula(formula.root, to_implies_not(formula.first))
        else:
            return Formula(formula.root,
                          to_implies_not(formula.first),
                          to_implies_not(formula.second))
    first = to_implies_not(formula.first)
    second = to_implies_not(formula.second)
    if formula.root == '&':
        return Formula('~', Formula('->', first, Formula('~', second)))
    if formula.root == '|':
        return Formula('->', Formula('~', first), second)
    if formula.root == '+':
        left = Formula('->', first, Formula('~', second))
        right = Formula('->', second, Formula('~', first))
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '<->':
        left = Formula('->', first, second)
        right = Formula('->', second, first)
        return Formula('~', Formula('->', left, Formula('~', right)))
    if formula.root == '-&':
        return Formula('->', first, Formula('~', second))
    if formula.root == '-|':
        return Formula('~', Formula('->', Formula('~', first), second))

def to_implies_false(formula: Formula) -> Formula:
    # Сначала преобразуем в -> и ~
    imp_not = to_implies_not(formula)

    def convert(expr):
        if is_variable(expr.root):
            return expr
        if expr.root == 'F':
            return expr
        if expr.root == '~':
            return Formula('->', convert(expr.first), Formula('F'))
        if expr.root == '->':
            return Formula('->', convert(expr.first), convert(expr.second))

    return convert(imp_not)