; Kea indentation rules for editors.
; Kea is indentation-sensitive — these rules tell editors when to
; increase or decrease indent level.

; Indent after declaration/expression openers
[
  (function_declaration)
  (expr_declaration)
  (effect_declaration)
  (trait_definition)
  (impl_block)
  (struct_definition)
  (test_declaration)
  (if_expression)
  (case_expression)
  (cond_expression)
  (handle_expression)
  (for_expression)
  (while_expression)
  (lambda_expression)
] @indent

; Dedent at keywords that start a peer-level clause
["else" "then"] @indent.dedent
