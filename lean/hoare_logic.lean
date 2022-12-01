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

namespace IncLoHoare

/-! ## Big step semantics -/

inductive big_step : IncLoLang.stmt × option IncLoLang.state → option IncLoLang.state → Prop
| skip {s} :
  big_step (IncLoLang.stmt.skip, s) s
| assign {x f s} :
  big_step (IncLoLang.stmt.assign x f, some s) (some (s{x ↦ f s}))
| seq {S T s t u} (hS : big_step (S, s) t)
    (hT : big_step (T, t) u) :
  big_step (S ;; T, s) u
-- | ite_true {b : IncLoLang.state → Prop} {S T s t} (hcond : b s)
--     (hbody : big_step (S, s) t) :
--   big_step (IncLoLang.stmt.ite b S T, s) t
-- | ite_false {b : IncLoLang.state → Prop} {S T s t} (hcond : ¬ b s)
--     (hbody : big_step (T, s) t) :
--   big_step (IncLoLang.stmt.ite b S T, s) t
-- | while_true {b : IncLoLang.state → Prop} {S s t u} (hcond : b s)
--     (hbody : big_step (S, s) t)
--     (hrest : big_step (IncLoLang.stmt.while b S, t) u) :
--   big_step (IncLoLang.stmt.while b S, s) u
-- | while_false {b : IncLoLang.state → Prop} {S s} (hcond : ¬ b s) :
--   big_step (IncLoLang.stmt.while b S, s) s

infix ` ⟹ ` : 110 := big_step

/-! ## Hoare Logic -/

def partial_hoare (P : (option IncLoLang.state) → Prop) (S : IncLoLang.stmt)
  (Q : (option IncLoLang.state) → Prop) : Prop := 
  ∀ s t, P s → (S, s) ⟹ t → Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` :=
  partial_hoare P S Q

namespace hoare_logic

lemma skip_intro { P: (option IncLoLang.state) -> Prop } : {* P *} IncLoLang.stmt.skip {* P *} :=
begin
  intros s t hs hst,
  cases hst,
  assumption,
end

lemma assign_intro (P : option IncLoLang.state → Prop) {x} {a : IncLoLang.state → ℕ} :
  {* λs, P (option.bind s (λ st, st{x ↦ a st})) *} IncLoLang.stmt.assign x a {* P *} :=
begin
  intros s t P hst,
  cases' hst,
  assumption,
end

lemma seq_intro {P Q R S T} (hS : {* P *} S {* Q *})
    (hT : {* Q *} T {* R *}) :
  {* P *} S ;; T {* R *} :=
begin
  intros s t hs hst,
  cases' hst,
  apply hT,
  { apply hS,
    { exact hs },
    { assumption } },
  { assumption }
end

lemma consequence {P P' Q Q' : option IncLoLang.state → Prop} {S}
    (h : {* P *} S {* Q *}) (hp : ∀s, P' s → P s)
    (hq : ∀s, Q s → Q' s) :
  {* P' *} S {* Q' *} :=
begin
  intros s t,
  assume hs : P' s,
  assume hst : (S, s) ⟹ t,
  show Q' t, from
    hq _ (h s t (hp s hs) hst),
end

end hoare_logic

end IncLoHoare