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
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'``, ``'&'``, and ``'|'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'``, ``'&'``, and
        ``'|'``.
    """
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('|', Formula('p'), Formula('~', Formula('p')))
        else:  # 'F'
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
        if formula.root == '+':  # XOR
            return Formula('|', 
                          Formula('&', first, Formula('~', second)),
                          Formula('&', Formula('~', first), second))
        if formula.root == '<->':  # IFF
            return Formula('|',
                          Formula('&', first, second),
                          Formula('&', Formula('~', first), Formula('~', second)))
        if formula.root == '-&':  # NAND
            return Formula('~', Formula('&', first, second))
        if formula.root == '-|':  # NOR
            return Formula('~', Formula('|', first, second))

def to_not_and(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'~'`` and ``'&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'~'`` and ``'&'``.
    """
    # First convert to ~, &, |
    not_and_or_formula = to_not_and_or(formula)
    
    def convert(expr):
        if is_variable(expr.root):
            return expr
        if is_constant(expr.root):
            # Convert T/F using ~ and &
            if expr.root == 'T':
                return Formula('~', Formula('&', Formula('p'), Formula('~', Formula('p'))))
            else:  # 'F'
                return Formula('&', Formula('p'), Formula('~', Formula('p')))
        if is_unary(expr.root):
            return Formula('~', convert(expr.first))
        if expr.root == '&':
            return Formula('&', convert(expr.first), convert(expr.second))
        if expr.root == '|':
            # De Morgan's law: (a | b) = ~(~a & ~b)
            return Formula('~', 
                          Formula('&', 
                                 Formula('~', convert(expr.first)),
                                 Formula('~', convert(expr.second))))
    
    return convert(not_and_or_formula)

def to_nand(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'-&'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'-&'``.
    """
    # First convert to ~ and &
    not_and_formula = to_not_and(formula)
    
    def convert(expr):
        if is_variable(expr.root):
            return expr
        if is_unary(expr.root):
            # ~a = (a -& a)
            arg = convert(expr.first)
            return Formula('-&', arg, arg)
        if expr.root == '&':
            # (a & b) = ((a -& b) -& (a -& b))
            first = convert(expr.first)
            second = convert(expr.second)
            nand_ab = Formula('-&', first, second)
            return Formula('-&', nand_ab, nand_ab)
    
    return convert(not_and_formula)

def to_implies_not(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'~'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'~'``.
    """
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('p'), Formula('p'))
        else:  # 'F'
            return Formula('~', Formula('->', Formula('p'), Formula('p')))
            
    if is_variable(formula.root):
        return formula
        
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
        
    if is_binary(formula.root):
        first = to_implies_not(formula.first)
        second = to_implies_not(formula.second)
        
        if formula.root == '&':
            # (a & b) = ~(a -> ~b)
            return Formula('~', Formula('->', first, Formula('~', second)))
            
        if formula.root == '|':
            # (a | b) = ~a -> b
            return Formula('->', Formula('~', first), second)
            
        if formula.root == '->':
            # (a -> b) = a -> b
            return Formula('->', first, second)
            
        if formula.root == '+':  # XOR
            # (a + b) = ~((a -> ~b) -> ~(b -> ~a))
            left = Formula('->', first, Formula('~', second))
            right = Formula('->', second, Formula('~', first))
            return Formula('~', Formula('->', left, Formula('~', right)))
            
        if formula.root == '<->':  # IFF
            # (a <-> b) = ~(~(a -> b) -> ~(b -> a))
            left = Formula('->', first, second)
            right = Formula('->', second, first)
            return Formula('~', Formula('->', Formula('~', left), Formula('~', right)))
            
        if formula.root == '-&':  # NAND
            # (a -& b) = ~(a & b) = ~(~(a -> ~b)) = a -> ~b
            return Formula('->', first, Formula('~', second))
            
        if formula.root == '-|':  # NOR
            # (a -| b) = ~(a | b) = ~(~a -> b)
            return Formula('~', Formula('->', Formula('~', first), second))

def to_implies_false(formula: Formula) -> Formula:
    """Syntactically converts the given formula to an equivalent formula that
    contains no constants or operators beyond ``'->'`` and ``'F'``.

    Parameters:
        formula: formula to convert.

    Returns:
        A formula that has the same truth table as the given formula, but
        contains no constants or operators beyond ``'->'`` and ``'F'``.
    """
    # First convert to -> and ~
    implies_not_formula = to_implies_not(formula)
    
    def convert(expr):
        if is_variable(expr.root):
            return expr
            
        if expr.root == 'F':
            return Formula('F')
            
        if expr.root == '~':
            # ~a = (a -> F)
            return Formula('->', convert(expr.first), Formula('F'))
            
        if expr.root == '->':
            return Formula('->', convert(expr.first), convert(expr.second))
    
    return convert(implies_not_formula)