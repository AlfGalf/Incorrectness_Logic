
import lean.language
import lean.incorrectness_logic
import lean.completeness

inductive lang : Type
| skip            : lang
| assign          : string → IncLoLang.expression → lang
| non_det_assign  : string → lang
| seq             : lang → lang → lang
| if_             : IncLoLang.expression → lang → lang → lang
| loop_           : IncLoLang.expression → lang → lang
| error           : lang

def lang.to_stmt : lang → IncLoLang.stmt 
| lang.skip := IncLoLang.stmt.skip
| (lang.assign s e) := IncLoLang.stmt.assign s e
| (lang.non_det_assign s) := IncLoLang.stmt.non_det_assign s
| (lang.seq C₁ C₂) := IncLoLang.stmt.seq (C₁.to_stmt) (C₂.to_stmt)
| (lang.if_ e bt bf) := (IncLoLang.stmt.assumes (λ st, (e st: ℤ) = 0) ;; (bt.to_stmt)) <+> (IncLoLang.stmt.assumes (λ st, (e st: ℤ) ≠ 0) ;; (bf.to_stmt))
| (lang.loop_ e l) := (IncLoLang.stmt.assumes (λ st, (e st: ℤ) = 0) ;; (l.to_stmt))** ;; IncLoLang.stmt.assumes (λ st, (e st: ℤ) ≠ 0)
| lang.error := IncLoLang.stmt.error

notation a `;>` b := lang.seq a b

def loop1 : IncLoLang.stmt :=
  (
    lang.non_det_assign "n" ;> 
    lang.assign "x" (λ _, 0) ;> 
    lang.loop_ (λ σ, if (σ "n": ℤ) > 0 then (0: ℤ) else (1: ℤ)) (
      lang.assign "x" (λ σ, σ "x" + σ "n") ;>
      lang.non_det_assign "n"
    )
  ).to_stmt

lemma ex_pt_1 : [* λ σ, σ "x" = 0 *]
      (IncLoLang.stmt.assumes (λ (st : IncLoLang.state), ite (st "n" > 0) (0: ℤ) (1: ℤ) = 0) ;;
         (lang.assign "x" (λ (σ : IncLoLang.state), σ "x" + σ "n");>lang.non_det_assign "n").to_stmt)** [* IncLoLang.LogicType.ok: λ σ , σ "x" > 0 *] := 
begin
  apply IncLogic.iterate_non_zero_incorrect,
  apply IncLogic.seq_normal_incorrect (λ σ, σ "x" = 0),
  {
    exact IncLogic.iterate_zero_incorrect (λ σ, σ "x" = 0),
  },
  {
    apply IncLogic.seq_normal_incorrect (λ σ, σ "x" = 0 ∧ σ "n" > 0),
    {
      have X := IncLogic.assume_incorrect_ok (λ σ, σ "x" = 0) (λ σ, ite (σ "n" > 0) 0 1 = 0),
      simp at X ⊢,
      apply IncLogic.consequence_incorrect X,
      { 
        intros σ hσ, 
        split,
        finish,
        exact ((lt_iff_not_ge 0 (σ "n")).1 hσ.right),
      }, 
      { intros σ, finish, },
    },
    {
      repeat {rw lang.to_stmt},
      apply IncLogic.seq_normal_incorrect (λ σ, σ "x" > 0 ∧ σ "n" = σ "x"),
      {
        apply IncLogic.consequence_incorrect (
          IncLogic.assignment_correct 
            (λ (σ : IncLoLang.state), σ "x" = 0 ∧ σ "n" > 0)
            "x"
            (λ (σ : IncLoLang.state), σ "x" + σ "n")
        ),
        {
          rintros σ ⟨ hσl, hσr ⟩ ,
          use 0,
          unfold IncLoLang.prop.update_val,
          have hx: "n" ≠ "x", {finish,},
          split,
          split,
          {finish,},
          { simp[hx], finish, },
          { simp[hx], exact eq.symm hσr, }
        },
        { intros σ hσ, exact hσ, }
      },
      {
        apply IncLogic.consequence_incorrect (
          IncLogic.non_det_assignment_incorrect (λ σ, σ "x" > 0 ∧ σ "n" = σ "x") "n"
        ),
        {
          intros σ hσ,
          use (σ "x"),
          unfold IncLoLang.prop.update_val,
          have hx: "n" ≠ "x", {finish,},
          simp[hx, ne.symm hx],

          exact hσ,
        },
        { intros σ hσ, exact hσ, }
      }
    }
  },
end

lemma ex_pt_2 : [* λ σ, σ "x" = 0 *]
      (IncLoLang.stmt.assumes (λ (st : IncLoLang.state), ite (st "n" > 0) (0:ℤ) (1:ℤ) = 0) ;;
         (lang.assign "x" (λ (σ : IncLoLang.state), σ "x" + σ "n");>lang.non_det_assign "n").to_stmt)** [* IncLoLang.LogicType.ok: λ σ , σ "x" = 0 ∧ σ "n" ≤ 0 *] := 
begin
  apply IncLogic.consequence_incorrect (IncLogic.iterate_zero_incorrect (λ σ, σ "x" = 0)),
  { intros σ hσ , exact hσ.left, },
  { intros σ hσ, exact hσ, }
end

example: [* (λ _, true) *]loop1[* IncLoLang.LogicType.ok: λ σ, σ "x" ≥ 0 ∧ σ "n" ≤ 0 *] :=
begin
  unfold loop1,
  apply IncLogic.seq_normal_incorrect (λ σ, σ "x" = 0),
  {
    -- Prove starting assumption
    apply IncLogic.seq_normal_incorrect (λ σ, true),
    {
      have X := IncLogic.non_det_assignment_incorrect (λ _, true) "n",
      apply IncLogic.consequence_incorrect X,
      { intros σ t, use 1, },
      { finish, }
    },
    {
      rw lang.to_stmt,
      have X := IncLogic.assignment_correct (λ _, true) "x" (λ _, 0),
      apply IncLogic.consequence_incorrect X,
      {
        intros σ hσ,
        use 0, split,
        { rw IncLoLang.prop.update_val, exact trivial, },
        { rw hσ, }
      },
      { finish, }
    }
  },
  {
    rw lang.to_stmt,

    apply IncLogic.seq_normal_incorrect (λ σ, σ "x" > 0 ∨ (σ "x" = 0 ∧ σ "n" ≤ 0) ),
    {
      apply IncLogic.consequence_incorrect (
        IncLogic.disjunction_incorrect (λ σ, σ "x" = 0) (λ σ, σ "x" = 0) (λ σ, σ "x" > 0) (λ σ, σ "x" = 0 ∧ σ "n" ≤ 0) ((IncLoLang.stmt.assumes (λ (st : IncLoLang.state), ite (st "n" > 0) (0: ℤ) (1: ℤ) = 0) ;;
         (lang.assign "x" (λ (σ : IncLoLang.state), σ "x" + σ "n");>lang.non_det_assign "n").to_stmt)**) IncLoLang.LogicType.ok ex_pt_1 ex_pt_2
      ),
      {
        intros σ hσ,
        exact hσ,  
      },
      {
        intros σ hσ, 
        cases hσ ; exact hσ,
      },
    },
    {
      apply IncLogic.consequence_incorrect (IncLogic.assume_incorrect_ok (λ σ, σ "x" > 0 ∨ (σ "x" = 0 ∧ σ "n" ≤ 0)) (λ (st : IncLoLang.state), ite (st "n" > 0) (0: ℤ) (1 : ℤ) ≠ 0)),
      {
        intros σ hσ,
        split,
        {
          by_cases σ "x" = 0,
          { right, exact ⟨ h, hσ.right ⟩, },
          { left, exact (ne.symm h).lt_of_le hσ.left, }
        },
        { simp, exact hσ.right, }
      },
      { intros σ hσ, exact hσ, }
    }
  }
end
