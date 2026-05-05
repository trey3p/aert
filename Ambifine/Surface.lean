declare_syntax_cat ertType
declare_syntax_cat ertProp
declare_syntax_cat ertTerm
declare_syntax_cat ertStatement

-- Syntax for types
syntax "𝟙" : ertType
syntax "(" ident ":" ertType ")" " → " ertType : ertType
syntax "(" ident " : " ertType ")" " × " ertType : ertType
syntax ertType " + " ertType : ertType
syntax "(" ident " : " ertProp ")" " ⇒ " ertType : ertType
syntax "{" ident " : " ertType " | " ertProp "}" : ertType
syntax "∀" ident " : " ertType ", " ertType : ertType
syntax "∃" ident " : " ertType ", " ertType : ertType
syntax "ℕ" : ertType
syntax "(" ertType ")" : ertType

-- Syntax for props
syntax "⊤" : ertProp
syntax "⊥" : ertProp
syntax "(" ident " : " ertProp ")" " ⇒ " ertProp : ertProp
syntax "(" ident " : " ertProp ")" " ∧ " ertProp : ertProp
syntax ertProp " ∨ " ertProp : ertProp
syntax "∀" ident " : " ertType ", " ertProp : ertProp
syntax "∃" ident " : " ertType ", " ertProp : ertProp
syntax ertTerm " = " ertTerm : ertProp
syntax "(" ertProp ")" : ertProp

-- Syntax for terms
syntax ident : ertTerm
syntax "λ" ident " : " ertType " . " ertTerm : ertTerm
syntax ertTerm ertTerm : ertTerm
syntax "(" ertTerm ", " ertTerm ")" : ertTerm
syntax "let " "(" ident ", " ident ")" ":" ertType " = " ertTerm
  " in " ertTerm : ertTerm
syntax "inl" ertTerm : ertTerm
syntax "inr" ertTerm : ertTerm
syntax "cases" "[" ident ":" ertType "↦" ertType "]" ertTerm "|" "inl" ident "↦" ertTerm
  "|" "inr" ident "↦" ertTerm : ertTerm
syntax "λ" ident " : " ertProp " . " ertTerm : ertTerm
syntax ertTerm "(" term " : " ertProp ")" : ertTerm
syntax "{" ertTerm ", " term " :  " ertProp "}" : ertTerm
syntax "let" "{" ident ", " ident "}" " : " ertType " = "
  ertTerm " in " ertTerm : ertTerm
syntax "λ" "‖" ident " : " ertType "‖" " . " ertTerm : ertTerm
syntax ertTerm "(‖" ertTerm "‖)" : ertTerm
syntax "(" "‖" ertTerm "‖" ", " ertTerm ")" : ertTerm
syntax "let" "(" "‖" ident "‖" ", " ident ")" " : " ertType " = "
  ertTerm " in " ertTerm : ertTerm
syntax num : ertTerm
syntax "succ" : ertTerm
syntax "natrec" "[" ident "↦" ertType "]" ertTerm "|" ertTerm
  "|" "‖" "succ" ident "‖" ", " ident "↦" ertTerm : ertTerm
syntax "(" ertTerm ")" : ertTerm

syntax "def" ident " : " ertType " := " ertTerm : ertStatement

syntax (name := ert) "#lang" "ERT" ertStatement+ : command
