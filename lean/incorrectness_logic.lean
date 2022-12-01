
import algebra
import data.real.basic
import data.vector
import tactic.explode
import tactic.find
import tactic.induction
import tactic.linarith
import tactic.rcases
import tactic.rewrite
import tactic.ring_exp
import tactic.tidy
import tactic.where

import lean.language

namespace IncLoIncorrectness

inductive LogicType : Type
| er
| ok

inductive lang_semantics: IncLoLang.stmt -> LogicType -> (IncLoLang.state) -> (IncLoLang.state) -> Prop
| skip {s} :
  lang_semantics IncLoLang.stmt.skip LogicType.ok s s
| seq_ok {S T s t u} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T LogicType.ok t u) :
  lang_semantics(S ;; T) LogicType.ok s u
| seq_er {S T s t u} (H1: lang_semantics S LogicType.ok s t) (H2: lang_semantics T LogicType.er t u) : 
  lang_semantics (S ;; T) LogicType.er s u
| error {s}:
  lang_semantics IncLoLang.stmt.error LogicType.er s s
| assign {x s f} :
  lang_semantics (IncLoLang.stmt.assign x f) LogicType.ok s (s{x ↦ (f s)})

def post (ty: LogicType) (r: IncLoLang.stmt) (P: IncLoLang.state -> Prop) : IncLoLang.state -> Prop 
  := λ st, ∃ σ, P σ ∧ lang_semantics r ty σ st

/- TODO: Change encoding of state-/
/- state × ℕ -> prop -/

def incorrectness_logic (type: LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ state, Q state -> ((post type R) P) state

def hoare_logic (type: LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ state, ((post type R) P) state -> Q state

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` ty: 2 :=
  hoare_logic ty P S Q

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` ty: 2 :=
  incorrectness_logic ty P S Q

lemma hoare_skip_intro_ok { P: IncLoLang.state -> Prop } : {* P *} IncLoLang.stmt.skip {* P *} LogicType.ok:=
begin
  intros state h,

  rcases h with ⟨σ, ⟨h₁, h₂⟩⟩,

  cases h₂,
  finish,
end

lemma inc_skip_intro_er { P: IncLoLang.state -> Prop } : [* P *] IncLoLang.stmt.error [* P *] LogicType.er :=
begin
  intros state h,

  use state,

  split,
  {finish,},
  {
    exact lang_semantics.error
  },
end

-- lemma seq_intro_hoare {P Q R S T} (hS : {* P *} S {* Q *} LogicType.ok)
--     (hT : {* Q *} T {* R *} LogicType.ok) :
--   {* P *} S ;; T {* R *} LogicType.ok :=
-- begin
--   intros s t hs hst,
--   cases' hst,
--   apply hT,
--   { apply hS,
--     { exact hs },
--     { assumption } },
--   { assumption }
-- end

end IncLoIncorrectness