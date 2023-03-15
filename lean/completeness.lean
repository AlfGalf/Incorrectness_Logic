import lean.incorrectness_logic

namespace IncorrectnessCompleteness

-- inductive IncorrectnessProof (P Q: IncLoLang.prop) (C: IncLoLang.stmt) (ty: IncLoLang.LogicType): Prop
-- | empty_under_approx : (ty = IncLoLang.LogicType.er) → IncorrectnessProof
-- | consequence        : (∃ P' Q': IncLoLang.prop, (∀ σ, P' σ  → P σ) ∧ (∀ σ, Q σ  → Q' σ) ∧ (IncorrectnessProof P' Q' C ty)) → Prop
-- | disjunction        : (∃ P₁ P₂ Q₁ Q₂, (P = P₁ ∧ P₂) ∧ (Q = Q₁ ∧ Q₂) ∧ ([* P₁ *]C[* Q₁ *]ty) ∧ ([* P₁ *]C[* Q₁ *]ty)) → Prop
-- | unit_ok            : (C = IncLoLang.stmt.skip) → (ty = IncLoLang.LogicType.ok) → (P = Q) → IncorrectnessProof
-- | unit_er            : (C = IncLoLang.stmt.skip) → (ty = IncLoLang.LogicType.er) → (Q = λ σ, false) → IncorrectnessProof
-- | sequencing_short   : (∃ C₁ C₂, C = C₁ ;; C₂ ∧ ty=IncLoLang.LogicType.er ∧ [*P*]C₁[*Q*]IncLoLang.LogicType.er) → IncorrectnessProof
-- | sequencing_normal  : (∃ C₁ C₂ R, C = C₁ ;; C₂ ∧ ([*P*]C₁[*R*]IncLoLang.LogicType.ok) ∧ [*R*]C₂[*Q*]ty) → IncorrectnessProof
-- | iterate_zero       : (∃ D, C = D**) → (ty = IncLoLang.LogicType.ok) → (P = Q) → IncorrectnessProof
-- | backwards_vairent  : (ty = IncLoLang.LogicType.ok) → (∃ (N: ℕ) (R: ℕ → IncLoLang.prop), P = R 0 ∧ Q = R N ∧ (∀ n: ℕ, [* R n *]C[* R (n + 1) *]ty)) → IncorrectnessProof
-- | choice             : (∃ C₁ C₂, C = C₁ <+> C₂ ∧ (([*P*]C₁[*Q*]ty) ∨ ([*P*]C₂[*Q*]ty))) → IncorrectnessProof
-- | error_er           : (C = IncLoLang.stmt.error ∧ ty = IncLoLang.LogicType.er ∧ P = Q) → IncorrectnessProof
-- | error_ok           : (C = IncLoLang.stmt.error ∧ ty = IncLoLang.LogicType.ok ∧ Q = λ σ, false) → IncorrectnessProof
-- | assumes            : (C = IncLoLang.stmt.error ∧ ty = IncLoLang.LogicType.ok ∧ Q = λ σ, false) → IncorrectnessProof

inductive IncorrectnessProof : IncLoLang.prop → IncLoLang.stmt → IncLoLang.prop → IncLoLang.LogicType → Prop
| empty_under_approx {P: IncLoLang.prop} {ty: IncLoLang.LogicType} {C: IncLoLang.stmt}: 
  IncorrectnessProof P C (λ _, false) ty
| consequence {P Q P' Q': IncLoLang.prop} {ty: IncLoLang.LogicType} {C: IncLoLang.stmt} (Hp: ∀ σ, P σ → P' σ) (Hq: ∀ σ, Q' σ → Q σ) (H: IncorrectnessProof P C Q ty): 
  IncorrectnessProof P' C Q' ty
| disjunction {P₁ Q₁ P₂ Q₂: IncLoLang.prop} {ty: IncLoLang.LogicType} {C: IncLoLang.stmt} (H₁: IncorrectnessProof P₁ C Q₁ ty) (H₁: IncorrectnessProof P₂ C Q₂ ty): 
  IncorrectnessProof (λ σ, P₁ σ ∨ P₂ σ) C (λ σ, Q₁ σ ∨ Q₂ σ) ty
| unit_ok {P: IncLoLang.prop}: 
  IncorrectnessProof P IncLoLang.stmt.skip P IncLoLang.LogicType.ok
| unit_er {P: IncLoLang.prop}: 
  IncorrectnessProof P IncLoLang.stmt.skip (λ _, false) IncLoLang.LogicType.er
| sequencing_short {P Q: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} (H: IncorrectnessProof P C₁ Q IncLoLang.LogicType.er): 
  IncorrectnessProof P (C₁;;C₂) Q IncLoLang.LogicType.er
| sequencing_normal {P Q R: IncLoLang.prop} {C₁ C₂: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H₁: IncorrectnessProof P C₁ Q IncLoLang.LogicType.ok)
  (H₂: IncorrectnessProof Q C₂ R ty) : 
  IncorrectnessProof P (C₁;;C₂) R ty
| iterate_zero {P: IncLoLang.prop} {C: IncLoLang.stmt} :
  IncorrectnessProof P (C**) P IncLoLang.LogicType.ok
| iterate_non_zero {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType}
  (H: IncorrectnessProof P (C** ;; C) Q ty) :
  IncorrectnessProof P (C**) Q ty
| backwards_variant {N: ℕ} {P: ℕ → IncLoLang.prop} {C: IncLoLang.stmt} 
  (H: ∀ n, IncorrectnessProof (P n) C (P (n+1)) IncLoLang.LogicType.ok) :
  IncorrectnessProof (P 0) (C**) (P N) IncLoLang.LogicType.ok
-- | choice

lemma IncorectnessProof.soundness {P Q: IncLoLang.prop} {C: IncLoLang.stmt} {ty: IncLoLang.LogicType} :
  IncorrectnessProof P C Q ty → [* P *]C[* Q *]ty :=
begin
  intro h,
  induction h,

  case empty_under_approx { exact IncLogic.empty_under_incorrect, },
  case consequence { exact IncLogic.consequence_incorrect (h_ih) h_Hq h_Hp, },
  case disjunction { refine IncLogic.disjunction_incorrect h_ih_H₁ h_ih_H₁_1},
  case unit_ok { refine IncLogic.unit_incorrect_ok},
  case unit_er { refine IncLogic.unit_incorrect_err},
  case sequencing_short { refine IncLogic.seq_short_circuit_incorrect h_ih, },
  case sequencing_normal { refine IncLogic.seq_normal_incorrect h_ih_H₁ h_ih_H₂, },
  case iterate_zero { refine IncLogic.iterate_zero_incorrect, },
  case iterate_non_zero {exact IncLogic.star_seq h_ih,},
  case backwards_variant {exact IncLogic.backwards_variant h_ih h_N,},


end

end IncorrectnessCompleteness