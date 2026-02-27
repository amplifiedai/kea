; Kea local variable scoping for rename/go-to-definition.

; Scopes
(function_declaration) @local.scope
(expr_declaration) @local.scope
(lambda_expression) @local.scope
(case_arm) @local.scope
(cond_arm) @local.scope
(for_expression) @local.scope
(handle_expression) @local.scope
(operation_clause) @local.scope
(let_expression) @local.scope

; Definitions
(function_declaration
  name: (identifier) @local.definition)

(parameter
  pattern: (variable_pattern
    (identifier) @local.definition))

(lambda_parameter
  pattern: (variable_pattern
    (identifier) @local.definition))

(let_expression
  pattern: (variable_pattern
    (identifier) @local.definition))

(case_arm
  pattern: (variable_pattern
    (identifier) @local.definition))

(case_arm
  pattern: (constructor_pattern
    (variable_pattern
      (identifier) @local.definition)))

(for_expression
  pattern: (variable_pattern
    (identifier) @local.definition))

; References
(identifier) @local.reference
