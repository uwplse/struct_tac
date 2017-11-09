import ..src.struct_tact

inductive t
| C1 : int → t
| C2 : int → t
| C3 : int → t

def foo (xs : t × t) : int :=
let z := 10 in
match xs with
| (t.C1 i, t.C2 j) := i + j + z
| (t.C2 j, t.C1 i) := j + i + z
| (_, _) := 0
end

lemma nested_break_match :
   forall i j, foo (t.C2 i, t.C1 j) = foo (t.C1 j, t.C2 i) :=
begin
    intros,
    unfold foo,
    dsimp,
    break_match
end
