import ..src.struct_tact

@[auto] inductive rel : nat → Type
| a : rel 0
| b : rel 1
| c : rel 2

lemma test_1 : rel 2 :=
begin
    auto,
end
