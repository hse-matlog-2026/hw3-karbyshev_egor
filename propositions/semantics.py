# This file is part of the materials accompanying the book
# "Mathematical Logic through Python" by Gonczarowski and Nisan,
# Cambridge University Press. Book site: www.LogicThruPython.org
# (c) Yannai A. Gonczarowski and Noam Nisan, 2017-2025
# File name: propositions/semantics.py

"""Semantic analysis of propositional-logic constructs."""

from typing import AbstractSet, Iterable, Mapping, Sequence, Tuple

from propositions.syntax import *
from propositions.proofs import *
from itertools import product

Model = Mapping[str, bool]

def is_model(model: Model) -> bool:
    for key in model:
        if not is_variable(key):
            return False
    return True

def variables(model: Model) -> AbstractSet[str]:
    assert is_model(model)
    return model.keys()

def evaluate(formula: Formula, model: Model) -> bool:
    assert is_model(model)
    assert formula.variables().issubset(variables(model))
    if is_constant(formula.root):
        return formula.root == 'T'
    if is_variable(formula.root):
        return model[formula.root]
    if is_unary(formula.root):
        return not evaluate(formula.first, model)
    assert is_binary(formula.root)
    first_value = evaluate(formula.first, model)
    second_value = evaluate(formula.second, model)
    if formula.root == '&':
        return first_value and second_value
    if formula.root == '|':
        return first_value or second_value
    if formula.root == '->':
        return (not first_value) or second_value
    if formula.root == '+':
        return first_value != second_value
    if formula.root == '<->':
        return first_value == second_value
    if formula.root == '-&':
        return not (first_value and second_value)
    if formula.root == '-|':
        return not (first_value or second_value)
    raise ValueError('Unknown operator: ' + formula.root)

def all_models(variables: Sequence[str]) -> Iterable[Model]:
    for v in variables:
        assert is_variable(v)
    for values in product([False, True], repeat=len(variables)):
        yield dict(zip(variables, values))

def truth_values(formula: Formula, models: Iterable[Model]) -> Iterable[bool]:
    for model in models:
        yield evaluate(formula, model)

def print_truth_table(formula: Formula) -> None:
    variables_sorted = sorted(formula.variables())
    headers = list(variables_sorted) + [str(formula)]
    widths = [len(header) for header in headers]
    for i in range(len(widths)):
        if widths[i] < 1:
            widths[i] = 1

    def format_row(values: Sequence[str]) -> str:
        return '|' + '|'.join(' ' + value.ljust(width) + ' '
                              for value, width in zip(values, widths)) + '|'

    print(format_row(headers))
    print('|' + '|'.join('-' * (width + 2) for width in widths) + '|')
    for model in all_models(variables_sorted):
        values = [('T' if model[var] else 'F') for var in variables_sorted]
        values.append('T' if evaluate(formula, model) else 'F')
        print(format_row(values))

def is_tautology(formula: Formula) -> bool:
    return all(truth_values(formula, all_models(sorted(formula.variables()))))

def is_contradiction(formula: Formula) -> bool:
    return not any(truth_values(formula, all_models(sorted(formula.variables()))))

def is_satisfiable(formula: Formula) -> bool:
    return any(truth_values(formula, all_models(sorted(formula.variables()))))

def _synthesize_for_model(model: Model) -> Formula:
    assert is_model(model)
    assert len(model.keys()) > 0
    literals = []
    for variable in sorted(model.keys()):
        if model[variable]:
            literals.append(Formula(variable))
        else:
            literals.append(Formula('~', Formula(variable)))
    formula = literals[0]
    for literal in literals[1:]:
        formula = Formula('&', formula, literal)
    return formula

def synthesize(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    assert len(variables) > 0
    models = list(all_models(variables))
    clauses = []
    for model, value in zip(models, values):
        if value:
            clauses.append(_synthesize_for_model(model))
    if not clauses:
        first_var = variables[0]
        return Formula('&', Formula(first_var),
                       Formula('~', Formula(first_var)))
    formula = clauses[0]
    for clause in clauses[1:]:
        formula = Formula('|', formula, clause)
    return formula

def _synthesize_for_all_except_model(model: Model) -> Formula:
    assert is_model(model)
    assert len(model.keys()) > 0
    literals = []
    for variable in sorted(model.keys()):
        if model[variable]:
            literals.append(Formula('~', Formula(variable)))
        else:
            literals.append(Formula(variable))
    formula = literals[0]
    for literal in literals[1:]:
        formula = Formula('|', formula, literal)
    return formula

def synthesize_cnf(variables: Sequence[str], values: Iterable[bool]) -> Formula:
    assert len(variables) > 0
    models = list(all_models(variables))
    clauses = []
    for model, value in zip(models, values):
        if not value:
            clauses.append(_synthesize_for_all_except_model(model))
    if not clauses:
        first_var = variables[0]
        return Formula('|', Formula(first_var),
                       Formula('~', Formula(first_var)))
    formula = clauses[0]
    for clause in clauses[1:]:
        formula = Formula('&', formula, clause)
    return formula

def evaluate_inference(rule: InferenceRule, model: Model) -> bool:
    assert is_model(model)

def is_sound_inference(rule: InferenceRule) -> bool:
    pass