import Ambifine.Surface
import Lean
open Lean Meta Elab Command

@[command_elab ert]
def ertImpl : CommandElab := fun stx => do
  for i in stx[2].getArgs do
    logInfo m!"{i}"
  return

set_option pp.rawOnError true
#lang ERT
def test : ℕ := 3
def test2 : ℕ := 5
