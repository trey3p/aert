declare_syntax_cat ertType
declare_syntax_cat ertTerm
declare_syntax_cat ertStatement

-- Syntax for types
syntax "𝟙" : ertType
syntax "(" ident ":" ertType ")" " → " ertType : ertType
syntax "(" ident " : " ertType ")" " × " ertType : ertType
syntax ertType " + " ertType : ertType
syntax "(" ident " : " term ")" " ⇒ " ertType : ertType
syntax "{" ident " : " ertType " | " term "}" : ertType
syntax "∀" ident " : " ertType ", " ertType : ertType
syntax "∃" ident " : " ertType ", " ertType : ertType
syntax "ℕ" : ertType
syntax "(" ertType ")" : ertType
syntax "list " ertType : ertType

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
syntax "λ" ident " : " term " . " ertTerm : ertTerm
syntax ertTerm "(" term " : " term ")" : ertTerm
syntax "{" ertTerm ", " term " :  " term "}" " : " ertType : ertTerm
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
syntax ertTerm " :: " ertTerm : ertTerm
syntax "listrec" "[" "(" ident " : " ertType ")" "↦" ertType "]" ertTerm "|" ertTerm
  "|" ident ", " ident ", " ident "↦" ertTerm : ertTerm

syntax "def" ident " : " ertType " := " ertTerm : ertStatement
syntax "def" ident " : " term " := " term : ertStatement

syntax (name := ert) "#lang" "ERT" ertStatement+ : command
