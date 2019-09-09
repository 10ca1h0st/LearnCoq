Inductive day : Type :=
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday.

Definition next_weekday (d:day) : day :=
  match d with
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => monday
  | saturday  => monday
  | sunday    => monday
  end.

Compute (next_weekday friday).

Example test_next_weekday:(next_weekday (next_weekday monday)) = wednesday.

Proof. simpl. reflexivity. Qed.

Inductive bool : Type :=
    |true
    |false.

Definition andb (arg1:bool)(arg2:bool):bool:=
    match arg1 with
    |true=>arg2
    |false=>false
    end.

Compute (andb true false).

Example test_andb:(andb true false)=false.

Proof.
simpl.
reflexivity.
Qed.

Notation "x && y":=(andb x y). Example test_notation:true&&false=false.
Proof. simpl. reflexivity. Qed.

Print test_notation.

Definition rb (arg1:bool):bool:=
    match arg1 with
    |true=>false
    |false=>true
    end.


Definition nandb (arg1:bool) (arg2:bool):bool:=
    match arg1 with
    |false=>true
    |true=>rb arg2
    end.

Example test_nandb1: (nandb true false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb2: (nandb false false) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb3: (nandb false true) = true.
Proof. simpl. reflexivity. Qed.
Example test_nandb4: (nandb true true) = false.
Proof. simpl. reflexivity. Qed.

Check nandb.
Check true.
Check rb.
Check andb.

Inductive rgb : Type :=
  | red
  | green
  | blue.
Inductive color : Type :=
  | black
  | white
  | primary (p : rgb).

Definition monochrome (c : color) : bool :=
  match c with
  | black=>true
  | white=>true
  | primary q=>false
  end.
Example test1:(monochrome (primary red))=false.
Proof. simpl. reflexivity. Qed.

Example test2:primary red=primary red.
Proof. simpl. reflexivity. Qed.
Check (primary red).

Inductive bit:Type:=
    |B0
    |B1.

Inductive halfbyte:Type:=
    |bits(b3 b2 b1 b0:bit).

Definition all_zero(arg:halfbyte):bool:=
    match arg with
    |(bits B0 B0 B0 B0)=>true
    |(bits _ _ _ _)=>false
    (*|(bits B0 B0 B0 B0)=>true*)
    end.

Example test_all_zero:all_zero (bits B0 B0 B0 B0)=true.
Proof. simpl. reflexivity. Qed.

Module NatPlayground.

Inductive nat:Type:=
    |O
    |S (n:nat).

(*Definition pred(n:nat):nat:=
    match n with
    |O => O
    |S n_pre=>n_pre
    end.*)


End NatPlayground.
Check (S (S (S O))).

Fixpoint oddn(n:nat):bool:=
    match n with
    |O=>false
    |S O=>true
    |S (S m)=>oddn m
    end.

Compute (oddn 988).


Fixpoint plus (n m : nat):nat:=
    match n with
        |O => m
        |S n' => S (plus n' m)
    end.

Compute (plus (S O) (S (S O))).
Notation "x + y" := (plus x y).

Fixpoint minus (n m : nat):nat:=
    match n,m with
        |O,_ => O
        |S _,O => n
        |S n',S m' => minus n' m'
    end.
Notation "x - y" := (minus x y).

Fixpoint mult (n m : nat):nat:=
    match n with
        |O => O
        |S O => m
        |S n' => (mult n' m)+m
    end.

Compute (mult 3 15).
Notation "x * y" := (mult x y).

Fixpoint exp (base power : nat):nat:=
    match power with
        |O => O
        |S O => base
        |S power' => mult base (exp base power')
    end.

Compute (exp 3 4).
Notation "x ^ y" := (exp x y).
Compute (4^2).

Fixpoint factorial (n : nat):nat:=
    match n with
        |O => 1
        |S n' => mult n (factorial(n'))
    end.

Compute (factorial 5).





