(**************************************************************************)
(*                                                                        *)
(*     SMTCoq                                                             *)
(*     Copyright (C) 2011 - 2019                                          *)
(*                                                                        *)
(*     See file "AUTHORS" for the list of authors                         *)
(*                                                                        *)
(*   This file is distributed under the terms of the CeCILL-C licence     *)
(*                                                                        *)
(**************************************************************************)


(* This example tests the tactics in "real" condition: a part of the
   proof of correctness of insertion sort. It requires propositional
   reasoning, uninterpreted functions, and a bit of integer arithmetic.

   Ideally, the proof of each lemma should consists only on
   induction/destruct followed by a call to [smt]. What we currently
   lack:
     - we have to provide all the needed lemmas and unfold all the
       definitions
     - it requires too much from uninterpreted functions even when it is
       not needed
     - it sometimes fails (may be realted to the previous item)
 *)


Require Import SMTCoq.SMTCoq.
Require Import ZArith List Bool.

Local Open Scope Z_scope.


(* This will improve when SMTCoq works with SSReflect! *)

Lemma impl_implb (a b:bool) : (a -> b) <-> (a ---> b).
Proof. auto using (reflect_iff _ _ (ReflectFacts.implyP a b)). Qed.


Lemma eq_false b : b = false <-> negb b.
Proof. case b; intuition. Qed.


Section InsertionSort.

  Fixpoint insert (x:Z) (l:list Z) : list Z :=
    match l with
    | nil => x::nil
    | y::ys => if (x <=? y)%Z then x::y::ys else y::(insert x ys)
    end.

  Fixpoint sort (l:list Z) : list Z :=
    match l with
    | nil => nil
    | x::xs => insert x (sort xs)
    end.


  Section Spec.

    Fixpoint is_sorted (l:list Z) : bool :=
      match l with
      | nil => true
      | x::xs =>
        match xs with
        | nil => true
        | y::_ => (x <=? y)%Z && (is_sorted xs)
        end
      end.

    Fixpoint smaller (x:Z) (l:list Z) : bool :=
      match l with
      | nil => true
      | y::ys => (x <=? y)%Z && (smaller x ys)
      end.


    Lemma is_sorted_smaller x y ys :
      (((x <=? y)%Z && is_sorted (y :: ys)) ---> is_sorted (x :: ys)).
    Proof.
      destruct ys as [ |z zs].
      - simpl. smt.
      - change (is_sorted (y :: z :: zs)) with ((y <=? z)%Z && (is_sorted (z::zs))).
        change (is_sorted (x :: z :: zs)) with ((x <=? z)%Z && (is_sorted (z::zs))).
        (* [smt] or [verit] fail? *)
        assert (H:forall b, (x <=? y)%Z && ((y <=? z) && b) ---> (x <=? z) && b) by smt.
        apply H.
    Qed.


    Lemma is_sorted_cons x xs :
      (is_sorted (x::xs)) <---> (is_sorted xs && smaller x xs).
    Proof.
      induction xs as [ |y ys IHys].
      - reflexivity.
      - change (is_sorted (x :: y :: ys)) with ((x <=? y)%Z && (is_sorted (y::ys))).
        change (smaller x (y :: ys)) with ((x <=? y)%Z && (smaller x ys)).
        generalize (is_sorted_smaller x y ys). revert IHys. rewrite !impl_implb.
        (* Idem *)
        assert (H:forall a b c d, (a <---> b && c) --->
                                  ((x <=? y) && d ---> a) --->
                                  ((x <=? y) && d <--->
                                  d && ((x <=? y) && c))) by smt.
        apply H.
    Qed.


    Lemma insert_keeps_smaller x y ys :
      smaller y ys ---> (y <=? x) ---> smaller y (insert x ys).
    Proof.
      induction ys as [ |z zs IHzs].
      - simpl. smt.
      - simpl. case (x <=? z).
        + simpl.
          (* [smt] or [verit] require [Compec (list Z)] but they should not *)
          assert (H:forall a, (y <=? z) && a ---> (y <=? x) ---> (y <=? x) && ((y <=? z) && a)) by smt.
          apply H.
        + simpl. revert IHzs. rewrite impl_implb.
          (* Idem *)
          assert (H:forall a b, (a ---> (y <=? x) ---> b) ---> (y <=? z) && a ---> (y <=? x) ---> (y <=? z) && b) by smt.
          apply H.
    Qed.


    Lemma insert_keeps_sorted x l : is_sorted l -> is_sorted (insert x l).
    Proof.
      induction l as [ |y ys IHys].
      - reflexivity.
      - intro H. simpl. case_eq (x <=? y); intro Heq.
        + change ((x <=? y)%Z && (is_sorted (y::ys))). rewrite Heq, H. reflexivity.
        + rewrite eq_false in Heq.
          rewrite (eqb_prop _ _ (is_sorted_cons _ _)) in H.
          rewrite (eqb_prop _ _ (is_sorted_cons _ _)).
          generalize (insert_keeps_smaller x y ys).
          revert IHys H Heq. rewrite !impl_implb.
          (* Idem *)
          assert (H: forall a b c d, (a ---> b) ---> a && c ---> negb (x <=? y) ---> (c ---> (y <=? x) ---> d) ---> b && d) by smt.
          apply H.
    Qed.


    Theorem sort_sorts l : is_sorted (sort l).
    Proof.
      induction l as [ |x xs IHxs].
      - reflexivity.
      - simpl. now apply insert_keeps_sorted.
    Qed.

  End Spec.

End InsertionSort.
Print Assumptions sort_sorts.
(*
Axioms:
Structures.trace_fold_ind : forall (state step : Type) 
                              (P : state -> Prop)
                              (transition : state -> step -> state)
                              (t : Structures.trace step),
                            (forall (s0 : state) (i : int),
                             (i < Structures.trace_length t)%int = true ->
                             P s0 ->
                             P (transition s0 (Structures.trace_get t i))) ->
                            forall s0 : state,
                            P s0 -> P (Structures.trace_fold transition s0 t)
sub_spec : forall x y : int, [|x - y|]%int = ([|x|]%int - [|y|]%int) mod wB
BVList.proof_irrelevance : forall (P : Prop) (p1 p2 : P), p1 = p2
of_Z_spec : forall z : Z, [|of_Z z|]%int = z mod wB
lxor_spec : forall x y i : int, bit (x lxor y) i = xorb (bit x i) (bit y i)
ltb_length : forall (A : Type) (t : array A),
             (PArray.length t <= max_array_length)%int = true
lor_spec : forall x y i : int, bit (x lor y) i = bit x i || bit y i
length_set : forall (A : Type) (t : array A) (i : int) (a : A),
             PArray.length (t .[ i <- a])%array = PArray.length t
length_make : forall (A : Type) (size : int) (a : A),
              PArray.length (make size a) =
              (if (size <= max_array_length)%int
               then size
               else max_array_length)
get_set_same : forall (A : Type) (t : array A) (i : int) (a : A),
               (i < PArray.length t)%int = true ->
               ((t .[ i <- a]) .[ i])%array = a
get_set_other : forall (A : Type) (t : array A) (i j : int) (a : A),
                i <> j -> ((t .[ i <- a]) .[ j])%array = (t .[ j])%array
get_outofbound : forall (A : Type) (t : array A) (i : int),
                 (i < PArray.length t)%int = false ->
                 (t .[ i])%array = default t
get_make : forall (A : Type) (a : A) (size i : int),
           (make size a .[ i])%array = a
foldi_down_cont_lt : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                       (from downto : int) (cont : A -> B),
                     (from < downto)%int = true ->
                     foldi_down_cont f from downto cont = cont
foldi_down_cont_gt : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                       (from downto : int) (cont : A -> B),
                     (downto < from)%int = true ->
                     foldi_down_cont f from downto cont =
                     f from
                       (fun a' : A =>
                        foldi_down_cont f (from - 1) downto cont a')
foldi_down_cont_eq : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                       (from downto : int) (cont : A -> B),
                     from = downto ->
                     foldi_down_cont f from downto cont = f from cont
foldi_cont_lt : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                  (from to : int) (cont : A -> B),
                (from < to)%int = true ->
                foldi_cont f from to cont =
                f from (fun a' : A => foldi_cont f (from + 1) to cont a')
foldi_cont_gt : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                  (from to : int) (cont : A -> B),
                (to < from)%int = true -> foldi_cont f from to cont = cont
foldi_cont_eq : forall (A B : Type) (f : int -> (A -> B) -> A -> B)
                  (from to : int) (cont : A -> B),
                from = to -> foldi_cont f from to cont = f from cont
default_set : forall (A : Type) (t : array A) (i : int) (a : A),
              default (t .[ i <- a])%array = default t
default_make : forall (A : Type) (a : A) (size : int),
               default (make size a) = a
ClassicalEpsilon.constructive_indefinite_description : 
forall (A : Type) (P : A -> Prop), (exists x : A, P x) -> {x : A | P x}
compare_def_spec : forall x y : int, (x ?= y)%int = compare_def x y
Classical_Prop.classic : forall P : Prop, P \/ ~ P
cast_refl : forall i : int,
            cast i i = Some (fun (P : int -> Type) (H : P i) => H)
cast_diff : forall i j : int, (i == j)%int = false -> cast i j = None
bit_testbit : forall x i : int, bit x i = Z.testbit [|x|]%int [|i|]%int
bit_eq : forall i1 i2 : int,
         i1 = i2 <-> (forall i : int, bit i1 i = bit i2 i)
Cnf.afold_right_impb : forall (t_form : array form)
                         (interp_atom : int -> bool)
                         (interp_bvatom : int ->
                                          forall s : N,
                                          BVList.BITVECTOR_LIST.bitvector s)
                         (a : array int),
                       Misc.afold_right bool int true implb
                         (Lit.interp
                            (interp_state_var interp_atom interp_bvatom
                               t_form)) a =
                       C.interp
                         (interp_state_var interp_atom interp_bvatom t_form)
                         (to_list (Cnf.or_of_imp a))
Cnf.afold_left_or : forall (t_form : array form) (interp_atom : int -> bool)
                      (interp_bvatom : int ->
                                       forall s : N,
                                       BVList.BITVECTOR_LIST.bitvector s)
                      (a : array int),
                    Misc.afold_left bool int false orb
                      (Lit.interp
                         (interp_state_var interp_atom interp_bvatom t_form))
                      a =
                    C.interp
                      (interp_state_var interp_atom interp_bvatom t_form)
                      (to_list a)
Bva_checker.afold_left_or : forall (t_atom : array atom)
                              (t_form : array form) 
                              (t_i : array typ_compdec)
                              (t_func : array (tval t_i)) 
                              (a : array int),
                            Misc.afold_left bool int false orb
                              (Lit.interp
                                 (interp_state_var
                                    (interp_form_hatom t_i t_func t_atom)
                                    (interp_form_hatom_bv t_i t_func t_atom)
                                    t_form)) a =
                            C.interp
                              (interp_state_var
                                 (interp_form_hatom t_i t_func t_atom)
                                 (interp_form_hatom_bv t_i t_func t_atom)
                                 t_form) (to_list a)
Array_checker.afold_left_or : forall (t_form : array form)
                                (t_atom : array atom)
                                (t_i : array typ_compdec)
                                (t_func : array (tval t_i)) 
                                (a : array int),
                              Misc.afold_left bool int false orb
                                (Lit.interp
                                   (interp_state_var
                                      (interp_form_hatom t_i t_func t_atom)
                                      (interp_form_hatom_bv t_i t_func t_atom)
                                      t_form)) a =
                              C.interp
                                (interp_state_var
                                   (interp_form_hatom t_i t_func t_atom)
                                   (interp_form_hatom_bv t_i t_func t_atom)
                                   t_form) (to_list a)
Cnf.afold_left_and : forall (t_form : array form) 
                       (interp_atom : int -> bool)
                       (interp_bvatom : int ->
                                        forall s : N,
                                        BVList.BITVECTOR_LIST.bitvector s)
                       (a : array int),
                     Misc.afold_left bool int true andb
                       (Lit.interp
                          (interp_state_var interp_atom interp_bvatom t_form))
                       a =
                     forallb
                       (Lit.interp
                          (interp_state_var interp_atom interp_bvatom t_form))
                       (to_list a)
Bva_checker.afold_left_and : forall (t_atom : array atom)
                               (t_form : array form)
                               (t_i : array typ_compdec)
                               (t_func : array (tval t_i)) 
                               (a : array int),
                             Misc.afold_left bool int true andb
                               (Lit.interp
                                  (interp_state_var
                                     (interp_form_hatom t_i t_func t_atom)
                                     (interp_form_hatom_bv t_i t_func t_atom)
                                     t_form)) a =
                             forallb
                               (Lit.interp
                                  (interp_state_var
                                     (interp_form_hatom t_i t_func t_atom)
                                     (interp_form_hatom_bv t_i t_func t_atom)
                                     t_form)) (to_list a)
add_spec : forall x y : int, [|x + y|]%int = ([|x|]%int + [|y|]%int) mod wB
Z_land_bounded : forall i x y : Z,
                 0 <= x < 2 ^ i -> 0 <= y < 2 ^ i -> 0 <= Z.land x y < 2 ^ i
Cnf.Cinterp_neg : forall (t_form : array form) (interp_atom : int -> bool)
                    (interp_bvatom : int ->
                                     forall s : N,
                                     BVList.BITVECTOR_LIST.bitvector s)
                    (cl : list int),
                  C.interp
                    (interp_state_var interp_atom interp_bvatom t_form)
                    (map Lit.neg cl) =
                  negb
                    (forallb
                       (Lit.interp
                          (interp_state_var interp_atom interp_bvatom t_form))
                       cl)
*)
