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
syntax "list " ertType : ertType

-- Syntax for props
syntax "⊤" : ertProp
syntax "⊥" : ertProp
syntax "(" ident " : " ertProp ")" " ⇒ " ertProp : ertProp
syntax "(" ident " : " ertProp ")" " ∧ " ertProp : ertProp
syntax ertProp " ∨ " ertProp : ertProp
syntax "∀" ident " : " ertType ", " ertProp : ertProp
syntax "∃" ident " : " ertType ", " ertProp : ertProp
syntax ertTerm " = " "(" ertType ")" ertTerm : ertProp
syntax "(" ertProp ")" : ertProp

-- Syntax for terms
syntax ident : ertTerm
syntax "λ" ident " : " ertType " . " ertTerm : ertTerm
syntax "(" ertTerm " : " ertType ")" ertTerm : ertTerm
syntax "(" ertTerm ", " ertTerm ")" : ertTerm
syntax "let " "(" ident ", " ident ")" ":" ertType " = " ertTerm
  " in " ertTerm : ertTerm
syntax "(" "inl" ertTerm  ")" " : " ertType : ertTerm
syntax "(" "inr" ertTerm ")" " : " ertType : ertTerm
syntax "cases" "[" ident ":" ertType "↦" ertType "]" ertTerm "|" "inl" "(" ident " : " ertType ")" "↦" ertTerm
  "|" "inr" "(" ident " : " ertType ")" "↦" ertTerm : ertTerm
syntax "λ" ident " : " ertProp " . " ertTerm : ertTerm
syntax ertTerm "(" term " : " ertProp ")" : ertTerm
syntax "{" ertTerm ", " term " :  " ertProp "}" " : " ertType : ertTerm
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
syntax "nil" " : " ertType : ertTerm
syntax "(" ertTerm " : " ertType ")" " :: " ertTerm : ertTerm

syntax "def" ident " : " ertType " := " ertTerm : ertStatement
syntax "def" ident " : " ertProp " := " term : ertStatement

syntax (name := ert) "#lang" "ERT" ertStatement+ : command
