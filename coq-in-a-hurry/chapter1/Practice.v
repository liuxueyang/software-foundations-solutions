Check True.
Check 3.

(* the following two statement are same *)
Check (let f := fun x : nat => (x, x + 3) in f 3).
Check (let f (x : nat) := (x, x + 3) in f 3).

Locate "_ <= _".

Check (and True False).

Locate "_ /\ _".

Eval compute in
    let f := fun x : nat => (x * 3, x) in f 3.

Check (let f := fun a b c d e : nat => a + b + c + d + e
       in f 1 2 3 4 5).

Eval compute in
    let f := fun a b c d e : nat => a + b + c + d + e
    in f 1 2 3 4 5.