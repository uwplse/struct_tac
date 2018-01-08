import ..src.struct_tact

lemma break_conj_test (P Q Z : Prop) :
    P ∧ Q ∧ Z → Z :=
begin
    intros,
    break_conj,
end
