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
        return Formula(formula.root)
        
    if is_unary(formula.root):
        return Formula('~', to_implies_not(formula.first))
        
    if is_binary(formula.root):
        first = to_implies_not(formula.first)
        second = to_implies_not(formula.second)
        
        if formula.root == '&':
            # (a & b) = ~(a -> ~b)
            return Formula('~', Formula('->', first, Formula('~', second)))
            
        if formula.root == '|':
            # (a | b) = (~a -> b)
            return Formula('->', Formula('~', first), second)
            
        if formula.root == '->':
            # (a -> b) = a -> b
            return Formula('->', first, second)
            
        if formula.root == '+':
            # (a + b) = ~((a -> ~b) -> ~(~a -> b))
            left = Formula('->', first, Formula('~', second))
            right = Formula('->', Formula('~', first), second)
            return Formula('~', Formula('->', left, Formula('~', right)))
            
        if formula.root == '<->':
            # (a <-> b) = ~((a -> b) -> ~(b -> a))
            left = Formula('->', first, second)
            right = Formula('->', second, first)
            return Formula('~', Formula('->', left, Formula('~', right)))
            
        if formula.root == '-&':
            # (a -& b) = (a -> ~b)
            return Formula('->', first, Formula('~', second))
            
        if formula.root == '-|':
            # (a -| b) = ~(~a -> b)
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
    if is_constant(formula.root):
        if formula.root == 'T':
            return Formula('->', Formula('p'), Formula('p'))
        else:  # 'F'
            return Formula('F')
            
    if is_variable(formula.root):
        return Formula(formula.root)
        
    if is_unary(formula.root):
        if formula.root == '~':
            # ~a = (a -> F)
            return Formula('->', to_implies_false(formula.first), Formula('F'))
        return to_implies_false(formula.first)  # для других унарных (их нет)
        
    if is_binary(formula.root):
        first = to_implies_false(formula.first)
        second = to_implies_false(formula.second)
        
        if formula.root == '&':
            # (a & b) = (a -> (b -> F)) -> F
            return Formula('->', 
                          Formula('->', first, 
                                 Formula('->', second, Formula('F'))),
                          Formula('F'))
            
        if formula.root == '|':
            # (a | b) = (a -> F) -> b
            return Formula('->', Formula('->', first, Formula('F')), second)
            
        if formula.root == '->':
            # (a -> b) = a -> b
            return Formula('->', first, second)
            
        if formula.root == '+':
            # (a + b) = (a -> (b -> F)) -> (b -> (a -> F)) -> F
            left = Formula('->', first, Formula('->', second, Formula('F')))
            right = Formula('->', second, Formula('->', first, Formula('F')))
            return Formula('->', left, Formula('->', right, Formula('F')))
            
        if formula.root == '<->':
            # (a <-> b) = (a -> b) -> ((b -> a) -> F) -> F
            left = Formula('->', first, second)
            right = Formula('->', second, first)
            return Formula('->', left, Formula('->', right, Formula('F')))
            
        if formula.root == '-&':
            # (a -& b) = a -> (b -> F)
            return Formula('->', first, Formula('->', second, Formula('F')))
            
        if formula.root == '-|':
            # (a -| b) = (a -> F) -> (b -> F)
            return Formula('->', 
                          Formula('->', first, Formula('F')),
                          Formula('->', second, Formula('F')))