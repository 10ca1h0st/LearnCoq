From coqlearn Require Export wjm02.

Inductive natprod:Type:=
    |pair (n1 n2:nat).
Check (pair 3 5).

Definition fst (p:natprod) :nat:=
    match p with
        |pair x y=>x
    end.

Definition snd (p:natprod):nat:=
    match p with
        |pair x y=>y
    end.

Compute (snd (pair 2 4)).

Notation "( x , y )":=(pair x y).
Check (1,2).

Compute (snd (12,23)).

Definition swap_pair (p:natprod):natprod:=
    match p with
        |(x,y)=>(y,x)
    end.

Compute (swap_pair (1,2)).


Theorem surjective_pairing:forall p:natprod,p=(fst p,snd p).
Proof.
intros p.
destruct p as [n m] eqn:E.
simpl. reflexivity.
Qed.

Theorem snd_fst_is_swap:forall p:natprod,(snd p,fst p)=swap_pair p.
Proof.
intros p.
simpl.
destruct p as [n m].
simpl. reflexivity.
Qed.

Theorem fst_swap_is_snd:forall p:natprod,fst (swap_pair p)=snd p.
Proof.
intros p.
destruct p as [n m].
simpl. reflexivity.
Qed.

Inductive natlist:Type:=
    |nil
    |cons (n:nat) (l:natlist).

Definition mylist := cons 1 (cons 2 (cons 3 nil)).
Check (mylist).

Notation "x :: l":=(cons x l) (at level 60,right associativity).
Notation "[]":=nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Check ([1;2;3;4;5]).
(*just for test

Notation "[ x | .. | y ]" := (cons y .. (cons x nil) ..).

Check ([1|2|3|4|5]).

Definition fst_element_list (L:natlist):natlist:=
    match L with
        |nil=>nil
        |cons x L'=>cons x nil
    end.

Compute (fst_element_list [1|2|3|4|5]).
*)

Fixpoint repeat (n count : nat) : natlist :=
  match count with
  | O => []
  | S count' => n::(repeat n count')
  end.

Fixpoint length (l:natlist):nat:=
    match l with
        |nil=>0
        |h::t=>S (length t)
    end.

Compute (repeat 6 6).
Compute (length [1;2;3]).

Fixpoint app (L1 L2:natlist):natlist:=
    match L1 with
        |nil=>L2
        |h::t=>h::(app t L2)
    end.

Compute (app [1;2;3] [6;5;4]).

Compute (app [] []).

Notation "x ++ y":=(app x y) (right associativity,at level 60).

Definition hd (default:nat) (l:natlist):nat:=
    match l with
        |nil=>default
        |h::t=>h
    end.

Definition tl(l:natlist):natlist:=
    match l with
        |nil=>nil
        |h::t=>t
    end.

Fixpoint nonzeros(l:natlist):natlist:=
    match l with
        |nil=>nil
        |0::t=>nonzeros t
        |not0::t=>not0::(nonzeros t)
    end.

Compute (nonzeros [0;1;0;2;0;3;0;0]).
Compute (nonzeros [1;2;3]).
Compute (nonzeros [0;0;0]).


Fixpoint odd_fst_element(l:natlist):bool:=
    match l with
    |nil=>true
    |O::t=>false
    |(S O)::t=>true
    |(S (S m))::t=>oddn m
    end.

Compute (odd_fst_element [2;1;2;3]).


Fixpoint oddmembers(l:natlist):natlist:=
    match l,(odd_fst_element l) with
        |[],_=>[]
        |h::nil,false=>[]
        |h::t,false=>oddmembers t
        |h::t,true=>h::(oddmembers t)
    end.

Compute (oddmembers [12;43;5;32;0;12;11;666]).

Fixpoint countoddmembers (l:natlist):nat:=
    match l,(odd_fst_element l) with
        |[],_=>0
        |h::nil,false=>0
        |h::t,false=>countoddmembers t
        |h::t,true=>S (countoddmembers t)
    end.

Compute (countoddmembers [0;2;4]).

Theorem app_assoc:forall (l1 l2 l3:natlist),(l1++l2)++l3=l1++(l2++l3).
Proof.
intros l1 l2 l3.
induction l1 as [|n l' IHl'].
    -reflexivity.
    -simpl. rewrite->IHl'. simpl. reflexivity.
Qed.

Inductive natoption : Type :=
  | Some (n : nat)
  | None.

Inductive id:Type:=
    |Id (n:nat).

Definition eqb_id (x1 x2 : id) :=
  match x1, x2 with
  | Id n1, Id n2 => n1 =? n2
  end.

Module PartialMap.

Inductive partial_map:Type:=
    |empty
    |record (i:id) (v:nat) (m:partial_map).

Definition update (d:partial_map) (x:id) (value:nat):partial_map:=
    record x value d.

Fixpoint find (x:id) (d:partial_map):natoption:=
    match d with
        |empty=>None
        |record y v d'=>if eqb_id x y
                        then Some v
                        else find x d'
    end.

End PartialMap.




