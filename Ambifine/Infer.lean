import Ambifine.Untyped
import Ambifine.Context
import Ambifine.Subst
import Ambifine.UntypedToExpr
import Lean

open Lean Meta

namespace Untyped

-- Mirrors old-ert's Annot: distinguishes "e is a type/prop" from "e has type A"
inductive Annot where
  | sort : AnnotSort → Annot
  | exprType : Term → Annot
  | exprProp : Expr → Annot
deriving BEq, Repr

/-- Instantiate the loose bvars of a Hyp.prop's stored open Lean.Expr
    with the current fvars to obtain the Prop in the current scope.
    `Hyp.wk1` keeps the bvar indices aligned with the current de Bruijn depth,
    so this is a straight `instantiateRev`. -/
private def Hyp.propInScope (ty : Expr) (fvars : List Expr) : Expr :=
  ty.instantiate fvars.toArray

/--
inferType Γ fvars e returns the annotation for e if it can be inferred to be well-typed in Γ,
and throws an error with a message describing the failure otherwise.
Γ is a context within the aert type theory, fvars is a list of free variables corresponding to the conversion of Γ to lean.
e is a term withing the aert type theory.
Invariant:
  fvars[i] is always a valid fvar in the current MetaM local context.
  This requires the initkal fvars passed to inferType to be created by the caller's withLocalDeclD, and
  every extension to fvars in inferType to happen within a withLocalDeclD.
--/
def inferType (Γ : Ctx) (ρ : Env) (fvars : List Expr) (e : Term) : MetaM Annot :=
  match e with
  | Term.proof p Ty => do
    let p_inst := p.instantiate fvars.toArray
    let Ty_inst := Ty.instantiate fvars.toArray
    let p_ty ← Meta.inferType p_inst
    unless ← isDefEq p_ty Ty_inst do
      throwError m!"proof: type mismatch"
    return .exprProp Ty_inst
  | Term.expr e_expr => do
    let e_inst := e_expr.instantiate fvars.toArray
    unless ← Meta.isProp e_inst do
      throwError m!"Term.expr: expected a Prop, got {← ppExpr (← Meta.inferType e_inst)}"
    return .sort .prop
  -- Variables: ghost bindings are not directly usable as values
  | Term.var n =>
    match lookupVar Γ n with
    | some (.type ty) => return .exprType ty
    | some (.prop ty) => return .exprProp (Hyp.propInScope ty fvars)
    | _ => throwError m!"var: variable {n} not found or is ghost in context"

  -- ── Constants ─────────────────────────────────────────────────────────────

  | Term.const TermKind.unit  => return .sort .type
  | Term.const TermKind.nats  => return .sort .type
  | Term.const TermKind.nil   => return .exprType Term.unit
  | Term.const TermKind.zero  => return .exprType Term.nats
  -- succ : nats → nats  (pi nats nats is correct since nats is closed)
  | Term.const TermKind.succ  => return .exprType (Term.abs TermKind.pi Term.nats Term.nats)
  | Term.const (TermKind.definition name) => do
    match ρ.find? (·.name == name) with
    | some (.defn _ type _) => return .exprType type
    | some (.thm _ type _) => return .exprProp type
    | none => throwError m!"Unknown definition {name}"

  -- ── Type formers ──────────────────────────────────────────────────────────

  | Term.abs TermKind.pi A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.type A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"pi: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"pi: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.sigma A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.type A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"sigma: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"sigma: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.set A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.type A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .prop => return .sort .type
      | a => throwError m!"set: predicate {repr B} must be a prop, got {repr a}"
    | a => throwError m!"set: domain {repr A} must be a type, got {repr a}"

  | Term.assume φ A => do
    -- φ is an open Lean.Expr (bvars referring to outer ctx); check it is a Prop.
    let φ_inst := φ.instantiate fvars.toArray
    unless ← Meta.isProp φ_inst do
      throwError m!"assume: hypothesis must be a Prop"
    let res ← withLocalDeclD (← mkFreshUserName `x) φ_inst fun x =>
      inferType (Hyp.prop φ :: Γ) ρ (x :: fvars) A
    match res with
    | .sort .type => return .sort .type
    | a => throwError m!"assume: body {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.intersect A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"intersect: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"intersect: domain {repr A} must be a type, got {repr a}"

  | Term.abs TermKind.union A B => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) B
      match res with
      | .sort .type => return .sort .type
      | a => throwError m!"union: body {repr B} must be a type, got {repr a}"
    | a => throwError m!"union: domain {repr A} must be a type, got {repr a}"

  | Term.bin TermKind.coprod A B => do
    match ← inferType Γ ρ fvars A, ← inferType Γ ρ fvars B with
    | .sort .type, .sort .type => return .sort .type
    | aA, aB => throwError m!"coprod: both sides must be types, got {repr aA} and {repr aB}"

  -- ── Term introductions ────────────────────────────────────────────────────

  -- lam A s : pi A B  when s : B in (A :: Γ)
  | Term.abs TermKind.lam A s => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.type A :: Γ) ρ (x :: fvars) s
      match res with
      | .exprType B => return .exprType (Term.abs TermKind.pi A B)
      | a => throwError m!"lam: body {repr s} must have a type, got {repr a}"
    | a => throwError m!"lam: domain {repr A} must be a type, got {repr a}"

  -- lam_pr φ s : assume φ A  when s : A in (φ :: Γ)
  | Term.lam_pr φ s => do
    let φ_inst := φ.instantiate fvars.toArray
    unless ← Meta.isProp φ_inst do
      throwError m!"lam_pr: hypothesis must be a Prop"
    let res ← withLocalDeclD (← mkFreshUserName `x) φ_inst fun x =>
      inferType (Hyp.prop φ :: Γ) ρ (x :: fvars) s
    match res with
    | .exprType A => return .exprType (Term.assume φ A)
    | a => throwError m!"lam_pr: body {repr s} must have a type, got {repr a}"

  -- lam_irrel A s : intersect A B  when s : B in (‖A‖ :: Γ)
  | Term.abs TermKind.lam_irrel A s => do
    match ← inferType Γ ρ fvars A with
    | .sort .type =>
      let A_expr ← A.toExpr ρ fvars
      let res ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x =>
        inferType (Hyp.gst A :: Γ) ρ (x :: fvars) s
      match res with
      | .exprType B => return .exprType (Term.abs TermKind.intersect A B)
      | a => throwError m!"lam_irrel: body {repr s} must have a type, got {repr a}"
    | a => throwError m!"lam_irrel: domain {repr A} must be a type, got {repr a}"

  -- ── Function / proof eliminations ─────────────────────────────────────────

  -- app (pi A B) f x : term (B.subst0 x)
  | Term.app _ f x => do
    match ← inferType Γ ρ fvars f with
    | .exprType (Term.abs TermKind.pi A B) =>
      match ← inferType Γ ρ fvars x with
      | .exprType A' =>
          if A == A' then return .exprType (B.subst0 x)
          else throwError m!"app: argument type mismatch: expected {repr A}, got {repr A'}"
      | a => throwError m!"app: argument {repr x} must have a type, got {repr a}"
    | a => throwError m!"app: function {repr f} must have a pi type, got {repr a}"

  -- app_pr (assume φ A) l r : term (A.subst0 r)
  | Term.tri TermKind.app_pr _ l r => do
    match ← inferType Γ ρ fvars l with
    | .exprType (Term.assume φ A) =>
      match ← inferType Γ ρ fvars r with
      | .exprProp φ' =>
          let φ_inst := φ.instantiate fvars.toArray
          unless ← isDefEq φ_inst φ' do
            throwError m!"app_pr: proof type mismatch"
          return .exprType (A.subst0 r)
      | a => throwError m!"app_pr: right argument {repr r} must be a proof, got {repr a}"
    | a => throwError m!"app_pr: left argument {repr l} must have an assume type, got {repr a}"

  -- app_irrel (intersect A B) l r : term (B.subst0 r)
  -- r is a ghost argument: checked under Γ.upgrade
  | Term.tri TermKind.app_irrel _ l r => do
    match ← inferType Γ ρ fvars l with
    | .exprType (Term.abs TermKind.intersect A B) =>
      match ← inferType (Ctx.upgrade Γ) ρ fvars r with
      | .exprType A' =>
          if A == A' then return .exprType (B.subst0 r)
          else throwError m!"app_irrel: argument type mismatch: expected {repr A}, got {repr A'}"
      | a => throwError m!"app_irrel: right argument {repr r} must have a type, got {repr a}"
    | a => throwError m!"app_irrel: left argument {repr l} must have an intersect type, got {repr a}"

  -- ── Dependent pair / set / union introductions ─────────────────────────────

  -- pair l r : term (sigma A (B_r.wk1))
  | Term.bin TermKind.pair l r => do
    match ← inferType Γ ρ fvars l, ← inferType Γ ρ fvars r with
    | .exprType A, .exprType B_r =>
        return .exprType (Term.abs TermKind.sigma A B_r.wk1)
    | aL, aR => throwError m!"pair: both components must have types, got {repr aL} and {repr aR}"

  -- elem l r : term (set A P)
  | Term.elem l r Ty => do
    match Ty with
    | .set domTy (.expr P_expr) =>
      match ← inferType Γ ρ fvars l, ← inferType Γ ρ fvars r with
      | .exprType A, .exprProp φ_r =>
        unless domTy == A do
          throwError m!"elem: expected domain type to be {repr domTy}, got {repr A}"
        let l_expr ← l.toExpr ρ fvars
        let instantiatedPredicate := P_expr.instantiate (l_expr :: fvars).toArray
        unless ← isDefEq φ_r instantiatedPredicate do
          throwError m!"elem: proof has the wrong type"
        return .exprType Ty
      | aL, aR => throwError m!"elem: expected (type, prop), got {repr aL} and {repr aR}"
    | x => throwError m!"elem: expected type to be a set with a Lean prop predicate, got {repr x}"

  -- repr l r : term (union A (B_r.wk1))
  | Term.bin TermKind.repr l r => do
    match ← inferType (Ctx.upgrade Γ) ρ fvars l, ← inferType Γ ρ fvars r with
    | .exprType A, .exprType B_r =>
        return .exprType (Term.abs TermKind.union A B_r.wk1)
    | aL, aR => throwError m!"repr: both components must have types, got {repr aL} and {repr aR}"

  -- ── Natural number recursion ──────────────────────────────────────────────

  | Term.nr (TermKind.natrec .type) C e z s => do
    let nats_expr ← Term.nats.toExpr ρ fvars
    let res_C ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar =>
      inferType (Hyp.type Term.nats :: Γ) ρ (n_fvar :: fvars) C
    match res_C with
    | .sort .type =>
      match ← inferType Γ ρ fvars e with
      | .exprType (Term.const TermKind.nats) =>
        match ← inferType Γ ρ fvars z with
        | .exprType z_ty =>
          if z_ty == C.subst0 Term.zero then
            let succ_app := Term.tri TermKind.app
                              (Term.abs TermKind.pi Term.nats Term.nats)
                              Term.succ (Term.var 1)
            let step_ty  := (C.lift 1 1).alpha0 succ_app
            let step_ctx := Hyp.type C :: Hyp.gst Term.nats :: Γ
            let res_s ← withLocalDeclD (← mkFreshUserName `n) nats_expr fun n_fvar => do
              let C_n ← C.toExpr ρ (n_fvar :: fvars)
              withLocalDeclD (← mkFreshUserName `ih) C_n fun ih_fvar =>
                inferType step_ctx ρ (ih_fvar :: n_fvar :: fvars) s
            match res_s with
            | .exprType s_ty =>
                if s_ty == step_ty then return .exprType (C.subst0 e)
                else throwError m!"natrec: step type mismatch: expected {repr step_ty}, got {repr s_ty}"
            | a => throwError m!"natrec: step {repr s} must have a type, got {repr a}"
          else throwError m!"natrec: base case type mismatch: expected {repr (C.subst0 Term.zero)}, got {repr z_ty}"
        | a => throwError m!"natrec: base case {repr z} must have a type, got {repr a}"
      | a => throwError m!"natrec: subject {repr e} must have type nats, got {repr a}"
    | a => throwError m!"natrec: motive {repr C} must be a type, got {repr a}"

  -- ── Coproduct introduction ────────────────────────────────────────────────

  | Term.bin (TermKind.inj b) annot t => do
    match annot with
    | Term.bin TermKind.coprod A B =>
      match ← inferType Γ ρ fvars annot with
      | .sort .type =>
        match ← inferType Γ ρ fvars t with
        | .exprType T =>
          if b.val == 0 && T == A then
            return .exprType (Term.bin TermKind.coprod A B)
          else
            return .exprType (Term.bin TermKind.coprod A B)
        | a => throwError m!"inj: term {repr t} must have a type, got {repr a}"
      | a => throwError m!"inj: annotation {repr annot} must be a type, got {repr a}"
    | _ => throwError m!"inj: annotation must be a coprod type"

  -- ── Coproduct elimination ─────────────────────────────────────────────────

  | Term.cases (TermKind.case .type) K d l r => do
    match ← inferType Γ ρ fvars d with
    | .exprType (Term.bin TermKind.coprod A B) =>
      match K with
      | Term.abs TermKind.lam _ C =>
        let A_expr ← A.toExpr ρ fvars
        let B_expr ← B.toExpr ρ fvars
        let l_ty := C.alpha0 (Term.bin (TermKind.inj (0 : Fin 2)) B.wk1 (Term.var 0))
        let r_ty := C.alpha0 (Term.bin (TermKind.inj (1 : Fin 2)) A.wk1 (Term.var 0))
        let l_result ← withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar =>
          inferType (Hyp.type A :: Γ) ρ (x_fvar :: fvars) l
        let r_result ← withLocalDeclD (← mkFreshUserName `y) B_expr fun y_fvar =>
          inferType (Hyp.type B :: Γ) ρ (y_fvar :: fvars) r
        match l_result, r_result with
        | .exprType l_ty', .exprType r_ty' =>
          if l_ty' == l_ty && r_ty' == r_ty then
            return .exprType (C.subst0 d)
          else throwError m!"case: branch type mismatch"
        | aL, aR => throwError m!"case: branches must have types, got {repr aL} and {repr aR}"
      | _ => throwError m!"case: motive {repr K} must be a lam"
    | a => throwError m!"case: discriminant {repr d} must have coprod type, got {repr a}"

  -- ── Dependent pair / set / union eliminations ────────────────────────────

  | Term.let_bin (TermKind.let_pair .type) P e e' => do
    match P with
    | Term.abs TermKind.sigma A B =>
      match ← inferType Γ ρ fvars e with
      | .exprType P' =>
        if P' != P then throwError m!"let_pair: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr ρ (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.type B.wk1 :: Hyp.type A :: Γ)
                               ρ (y_fvar :: x_fvar :: fvars) e' with
            | .exprType T_ext => return .exprType T_ext
            | a => throwError m!"let_pair: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_pair: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_pair: annotation must be a sigma type"

  | Term.let_bin (TermKind.let_set .type) P e e' => do
    match P with
    | Term.abs TermKind.set A (.expr P_expr) =>
      match ← inferType Γ ρ fvars e with
      | .exprType P' =>
        if P' != P then throwError m!"let_set: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          -- predicate's bvars instantiated by (x_fvar + outer fvars) gives the prop in scope
          let φ_x := P_expr.instantiate (x_fvar :: fvars).toArray
          withLocalDeclD (← mkFreshUserName `h) φ_x fun h_fvar => do
            match ← inferType (Hyp.prop P_expr :: Hyp.type A :: Γ)
                               ρ (h_fvar :: x_fvar :: fvars) e' with
            | .exprType T_ext => return .exprType T_ext
            | a => throwError m!"let_set: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_set: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_set: annotation must be a set type with a Lean prop predicate"

  | Term.let_bin (TermKind.let_repr .type) P e e' => do
    match P with
    | Term.abs TermKind.union A B =>
      match ← inferType Γ ρ fvars e with
      | .exprType P' =>
        if P' != P then throwError m!"let_repr: scrutinee type {repr P'} does not match annotation {repr P}"
        let A_expr ← A.toExpr ρ fvars
        withLocalDeclD (← mkFreshUserName `x) A_expr fun x_fvar => do
          let B_x ← B.toExpr ρ (x_fvar :: fvars)
          withLocalDeclD (← mkFreshUserName `y) B_x fun y_fvar => do
            match ← inferType (Hyp.type B.wk1 :: Hyp.gst A :: Γ)
                               ρ (y_fvar :: x_fvar :: fvars) e' with
            | .exprType T_ext => return .exprType T_ext
            | a => throwError m!"let_repr: body {repr e'} must have a type, got {repr a}"
      | a => throwError m!"let_repr: scrutinee {repr e} must have a type, got {repr a}"
    | _ => throwError m!"let_repr: annotation must be a union type"

  | Term.list A => do
    match ← inferType Γ ρ fvars A with
    | .sort .type => return .sort .type
    | a => throwError m!"list: element type {repr A} must have a type, got {repr a}"
  | Term.em A => do
    match ← inferType Γ ρ fvars A with
    | .sort .type => return .exprType A
    | a => throwError m!"[]: element type {repr A} must have a type, got {repr a}"
  | Term.cons x xs => do
    match ← inferType Γ ρ fvars x with
    | .exprType x_ty =>
          match ← inferType Γ ρ fvars xs with
          | .exprType xs_ty =>
                if xs_ty == Term.list x_ty then return .exprType (Term.list x_ty)
                else throwError m!"cons: tail {repr xs} must have type list {repr x_ty}, got {repr xs_ty}"
          | a => throwError m!"cons: tail {repr xs} must have type list {repr x_ty}, got {repr a}"
    | a => throwError m!"cons: head {repr x} must have a type, got {repr a}"
  -- listrec .type C e nil_case cons_case : C.subst0 e
  --   e         : list A
  --   C         : type under (val (list A) type) :: Γ              (motive, var 0 = the list)
  --   nil_case  : term (C.subst0 (em A))                            (base)
  --   cons_case : term ((C.lift 1 2).alpha0 (cons (var 2) (var 1))) (step)
  --       in  (val (C.lift 1 1) type) :: (val (list A).wk1 type) :: (val A type) :: Γ
  --       conv: var 0 = ih, var 1 = tail, var 2 = head
  | Term.listrec _ C e nil_case cons_case => do
    match ← inferType Γ ρ fvars e with
    | .exprType (Term.list A) =>
      let A_expr     ← A.toExpr ρ fvars
      let list_A_expr ← (Term.list A).toExpr ρ fvars
      -- Check the motive under the list binder
      let res_C ← withLocalDeclD (← mkFreshUserName `xs) list_A_expr fun xs_fvar =>
        inferType (Hyp.type (Term.list A) :: Γ) ρ (xs_fvar :: fvars) C
      match res_C with
      | .sort .type =>
        let nil_ty := C.subst0 (Term.em A)
        match ← inferType Γ ρ fvars nil_case with
        | .exprType nil_case_ty =>
          if nil_case_ty == nil_ty then
            let cons_ctx :=
              Hyp.type (C.lift 1 1) ::
              Hyp.type (Term.list A).wk1 ::
              Hyp.type A :: Γ
            let cons_ty :=
              (C.lift 1 2).alpha0
                (Term.bin TermKind.cons (Term.var 2) (Term.var 1))
            let res_cons_case ←
              withLocalDeclD (← mkFreshUserName `hd) A_expr fun hd_fvar => do
                withLocalDeclD (← mkFreshUserName `tl) list_A_expr fun tl_fvar => do
                  let C_at_tl ← C.toExpr ρ (tl_fvar :: fvars)
                  withLocalDeclD (← mkFreshUserName `ih) C_at_tl fun ih_fvar =>
                    inferType cons_ctx ρ (ih_fvar :: tl_fvar :: hd_fvar :: fvars) cons_case
            match res_cons_case with
            | .exprType cons_case_ty =>
                if cons_case_ty == cons_ty then return .exprType (C.subst0 e)
                else throwError m!"listrec: cons case type mismatch: expected {repr cons_ty}, got {repr cons_case_ty}"
            | a => throwError m!"listrec: cons case {repr cons_case} must have a type, got {repr a}"
          else throwError m!"listrec: nil case type mismatch: expected {repr nil_ty}, got {repr nil_case_ty}"
        | a => throwError m!"listrec: nil case {repr nil_case} must have a type, got {repr a}"
      | a => throwError m!"listrec: motive {repr C} must be a type, got {repr a}"
    | a => throwError m!"listrec: subject {repr e} must have type list, got {repr a}"
  -- ── Not inferrable without annotation ────────────────────────────────────
  | _ => throwError m!"inferType: unsupported or non-inferrable term {repr e}"

end Untyped
