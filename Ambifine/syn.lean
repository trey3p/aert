
inductive Ty where
  | sum : Ty → Ty → Ty
  | unit : Ty
  | nat : Ty
  | prod : Ty → Ty → Ty
  | empty : Ty
  | arr : Ty → Ty → Ty

def Idx := Nat

inductive Expr where
  | var : Idx → Expr
  | z : Expr
  | succ : Expr → Expr
  | natrec : Expr → Expr → (Expr × Expr) → Expr
  | lam : Ty → Expr → Expr | app : Expr → Expr → Expr
  | tt : Expr
  | pair : Expr → Expr → Expr | elpair : Expr → Expr
  | inl : Expr → Expr | inr : Expr → Expr
  | case : Expr → (Expr × Expr ) → (Expr × Expr) → Expr

inductive RefTy where
  | prod : RefTy → RefTy → RefTy
  | arr : RefTy → RefTy → RefTy
  | unit : RefTy
  | sum : RefTy → RefTy → RefTy
  | larr : RefTy → RefTy → RefTy
  | subtype : RefTy → RefTy → RefTy
  | all : RefTy → RefTy → RefTy
  | exist : RefTy → RefTy → RefTy
  | nat : RefTy

inductive Prop where

inductive RefExpr where
  | tt : RefExpr
  | pair : RefExpr → RefExpr → RefExpr | gpair : RefExpr → RefExpr → RefExpr
  | elpair : RefExpr → RefExpr
  | var : Idx → RefExpr
  | lam : RefTy → RefExpr → RefExpr | plam : Prop → RefExpr → RefExpr | glam : RefExpr → RefExpr → RefExpr
  | app : RefExpr → RefExpr | gapp : RefExpr → RefExpr
  | inl : RefExpr → RefExpr | inr : RefExpr → RefExpr | case : RefExpr → (RefExpr × RefExpr ) → (RefExpr × RefExpr) → RefExpr
