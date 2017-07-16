(* 2017年07月16日 星期日 19时40分05秒 *)

Check True.

Check False.

Check (3 + 4).

Check (3, 3 < 5).

Check (fun x : nat => x < 3 \/ x >= 3).

Check (forall x : nat, x < 3 \/ (exists y : nat, x = y + 3)).

Inductive day : Type :=
| Monday : day
| Tuesday : day
| Wendsday : day
| Thursday : day
| Friday : day
| Saturday : day
| Sunday : day.

Definition next_weekday (d : day) : day :=
  match d with
  | Monday => Tuesday
  | Tuesday => Wendsday
  | Wendsday => Thursday
  | Thursday => Friday
  | Friday => Saturday
  | Saturday => Sunday
  | Sunday => Monday
  end.

Compute (next_weekday Monday).

Compute (next_weekday Sunday).

Example test_next_weekday :
  (next_weekday (next_weekday Saturday)) = Monday.

Proof. simpl. reflexivity. Qed.

Example test_next_weekday_error :
  (next_weekday Saturday) = Sunday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
| true : bool
| false : bool.

Definition negb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Definition orb (b1 : bool) (b2 : bool) : bool :=
  match b1 with
  | true => true
  | false => b2
  end.

Example test_orb1 : (orb true true) = true.
Proof. simpl. reflexivity. Qed.