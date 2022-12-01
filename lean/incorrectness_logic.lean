
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

inductive post: IncLoLang.stmt -> LogicType -> (IncLoLang.state) -> (IncLoLang.state) -> Prop
| seq_er {S T s t u} (H1: post S LogicType.ok s t) (H2: post T LogicType.er t u) : /- TODO: This needs to use post norm instead? How to encode? -/
  post (S ;; T) LogicType.er s u
| error {s}:
  post IncLoLang.stmt.error LogicType.er s s
| skip {s} :
  post IncLoLang.stmt.skip LogicType.ok s s
| assign {x s f} :
  post (IncLoLang.stmt.assign x f) LogicType.ok s (s{x ↦ (f s)})
| seq_ok {S T s t u} (H1: post S LogicType.ok s t) (H2: post T LogicType.ok t u) :
  post(S ;; T) LogicType.ok s u

def incorrectness_logic (ty: LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ s t, Q s -> post R ty t s -> P t

def hoare_logic (ty: LogicType) (P : (IncLoLang.state) → Prop) (R : IncLoLang.stmt)
  (Q : (IncLoLang.state) → Prop) : Prop := 
  ∀ s t, P s -> post R ty t s -> Q t

notation `{* ` P : 1 ` *} ` S : 1 ` {* ` Q : 1 ` *}` ty: 2 :=
  hoare_logic ty P S Q

notation `[* ` P : 1 ` *] ` S : 1 ` [* ` Q : 1 ` *]` ty: 2 :=
  hoare_logic ty P S Q

lemma hoare_skip_intro_ok { P: IncLoLang.state -> Prop } : {* P *} IncLoLang.stmt.skip {* P *} LogicType.ok:=
begin
  intros s t hs hst,
  cases hst,
  assumption,
end

lemma hoare_skip_intro_er { P: IncLoLang.state -> Prop } : {* P *} IncLoLang.stmt.skip {* P *} LogicType.er :=
begin
  intros s t hs hst,
  cases hst,
end


lemma inc_skip_intro_ok { P: IncLoLang.state -> Prop } : [* P *] IncLoLang.stmt.skip [* P *] LogicType.ok:=
begin
  intros s t hs hst,
  cases hst,
  assumption,
end

lemma inc_skip_intro_er { P: IncLoLang.state -> Prop } : [* P *] IncLoLang.stmt.skip [* P *] LogicType.er :=
begin
  intros s t hs hst,
  cases hst,
end

end IncLoIncorrectness