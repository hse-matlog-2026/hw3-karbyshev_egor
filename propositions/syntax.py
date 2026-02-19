def substitute_variables(self, substitution_map: Mapping[str, Formula]) -> \
        Formula:
    """Substitutes in the current formula, each variable name `v` that is a
    key in `substitution_map` with the formula `substitution_map[v]`.

    Parameters:
        substitution_map: mapping defining the substitutions to be
            performed.

    Returns:
        The formula resulting from performing all substitutions. Only
        variable name occurrences originating in the current formula are
        substituted (i.e., variable name occurrences originating in one of
        the specified substitutions are not subjected to additional
        substitutions).

    Examples:
        >>> Formula.parse('((p->p)|r)').substitute_variables(
        ...     {'p': Formula.parse('(q&r)'), 'r': Formula.parse('p')})
        (((q&r)->(q&r))|p)
    """
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