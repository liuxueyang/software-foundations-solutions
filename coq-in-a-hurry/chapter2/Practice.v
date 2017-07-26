(* Programming in Coq *)

Definition Example1 := fun x : nat => x * 3.
Definition Example2 (x : nat) := x * 3.

Check Example1.
Check Example2.

Eval compute in Example1 3.
Eval compute in Example2 4.

Print Example2.

Require Import Bool.

Search bool.

Eval compute in if true then 3 else 300.

