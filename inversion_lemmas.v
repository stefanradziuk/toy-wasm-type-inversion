From mathcomp Require Import ssreflect.
From Coq Require Import Program.Equality NArith ZArith_base List Extraction.
Import ListNotations.

Notation " P ** Q " := (prod P Q) (at level 95, right associativity).

Inductive term : Set :=
  | term_i32
  | term_f32
  | term_addi32
  | term_SEQ: term -> term -> term
.

Inductive value_type : Type :=
  | t_i32
  | t_f32
.

Inductive function_type : Type :=
  | Tf (t1s : list value_type) (t2s : list value_type)
.

Inductive typing : term -> function_type -> Prop :=
  | typing_term_i32 : typing term_i32 (Tf [] [t_i32])
  | typing_term_f32 : typing term_f32 (Tf [] [t_f32])
  | typing_term_addi32 : typing term_addi32 (Tf [t_i32; t_i32] [t_i32])
  | typing_weaken : forall t t1s t2s ts,
      typing t (Tf t1s t2s) -> typing t (Tf (ts ++ t1s) (ts ++ t2s))
  | typing_composition : forall t1 t2 t1s t2s t3s,
      typing t1 (Tf t1s t3s) ->
      typing t2 (Tf t3s t2s) ->
      typing (term_SEQ t1 t2) (Tf t1s t2s)
.

Lemma value_type_eq_dec : forall t1 t2 : value_type,
  {t1 = t2} + {t1 <> t2}.
Proof. decide equality. Qed.

Lemma value_type_list_eq_dec : forall l1 l2 : list value_type,
  {l1 = l2} + {l1 <> l2}.
Proof. apply List.list_eq_dec. apply value_type_eq_dec. Qed.

(* Typing inversion lemmas *)
Lemma term_i32_typing_inv : forall t t1s t2s,
  t = term_i32 ->
  typing t (Tf t1s t2s) ->
  {ts & t1s = ts ** t2s = ts ++ [t_i32]}.
Proof.
  intros t t1s t2s Hterm Htype.
  subst t.
  exists t1s; split => //.
  dependent induction Htype; subst => //.
  rewrite <- app_assoc; f_equal.
  by apply IHHtype.
Qed.

Lemma term_f32_typing_inv : forall t t1s t2s,
  t = term_f32 ->
  typing t (Tf t1s t2s) ->
  {ts & t1s = ts ** t2s = ts ++ [t_f32]}.
Proof.
  intros t t1s t2s Hterm Htype.
  subst t.
  exists t1s; split => //.
  dependent induction Htype; subst => //.
  rewrite <- app_assoc; f_equal.
  by apply IHHtype.
Qed.

(* XXX do these need sigma types or is exists fine?
 * since we don't want to have them at runtime anyway *)
(* TODO might need to use the type checker for this one too? *)
Lemma term_addi32_typing_inv : forall t t1s t2s,
  t = term_addi32 ->
  typing t (Tf t1s t2s) ->
  exists ts, t1s = ts ++ [t_i32; t_i32] ** t2s = ts ++ [t_i32].
Proof.
  intros t t1s t2s Hterm Htype.
  subst t.
  exists (removelast t2s); split.
Admitted.

(* We beed a type checker for the remaining lemmas *)

Definition type_checker_seq (t1 t2: term) (tf1 tf2: function_type): function_type :=
  (* TODO need to actually verify the types after the first n types
   * are correct *)
  match (tf1, tf2) with
  | (Tf t1_in t1_out, Tf t2_in t2_out) =>
      if length t1_out <=? length t2_in
      (* t2 consumes all or more than just the output of t1 *)
      then let ts := firstn (length t2_in - length t1_out) t2_in
      in Tf (ts ++ t1_in) (t2_out)
      (* t2 consumes some of the output of t1 *)
      else let ts := firstn (length t1_out - length t2_in) t1_out
      in Tf t1_in (ts ++ t2_out)
  end
.

(* assuming t well-typed, either:
 * * t2 consumes some of the output of t1 ('some' includes none or all)
 *   tf1=(Tf t1_in (ts ++ t2_in)) tf2=(Tf t2_in t2_out)
 *   (len t1_out >= t2_in)
 *   => so we need to consider weakened tf2:
 *   (Tf t1_in (ts ++ t2_in)) (Tf (ts ++ t2_in) (ts ++ t2_out))
 *   => the result is:
 *   Tf t1_in (ts ++ t2_out)
 *
 * * t2 consumes more than the output of t1,
 *   tf1=(Tf t1_in t1_out) tf2=(Tf (ts ++ t1_out) t2_out)
 *   (len t1_out <= t2_in)
 *   => so we need to consider weakened type of tf1:
 *   (Tf (ts ++ t1_in) (ts ++ t1_out)) (Tf (ts ++ t1_out) t2_out))
 *   => the result is:
 *   Tf (ts ++ t1_in) t2_out
 *)

(*
Tf qwer    efg
Tf abcdefg xyz
  -> weaken the first type as necessary
Tf abcdqwer abcdefg
Tf abcdefg  xyz
  -> result:
Tf abcdqwer xyz
 *)

Fixpoint type_checker (t: term): function_type :=
  match t with
  | term_i32 => Tf [] [t_i32]
  | term_f32 => Tf [] [t_f32]
  | term_addi32 => Tf [t_i32; t_i32] [t_i32]
  | term_SEQ t1 t2 =>
      type_checker_seq t1 t2 (type_checker t1) (type_checker t2)
  end.

Compute (type_checker term_i32).
Compute (type_checker term_f32).
Compute (type_checker (term_SEQ term_i32 term_f32)).
Compute (type_checker (term_SEQ (term_SEQ term_i32 term_i32) term_addi32)).

Axiom type_checker_implies_typing: forall t tf,
  type_checker t = tf ->
  typing t tf.

(* The weakenable relation needs to describe that the first function type
   can be weakened to the second. *)
Parameter weakenable: function_type -> function_type -> Prop.

Axiom typing_implies_type_checker_prefix: forall t tf,
  typing t tf ->
  weakenable (type_checker t) tf.

Lemma term_SEQ_typing_inv : forall t t1 t2 t1s t2s,
  t = term_SEQ t1 t2 ->
  typing t (Tf t1s t2s) ->
  {t3s & typing t1 (Tf t1s t3s) /\ typing t2 (Tf t3s t2s)}.
Proof.
Admitted.

(* Note: the program given to the interpreter must take no input
 * XXX should change it to instead pass around the stack of values *)
Definition interpret_one_step t tf_out (Htype : typing t (Tf [] tf_out)) : term.
Proof.
  destruct t as [| | |t1 t2] eqn:teq.
  (* term_i32 *)
  - apply term_i32.
  (* term_f32 *)
  - apply term_f32.
  (* term_addi32
   * binop with no values available - violates Htype *)
  - exfalso.
    apply term_addi32_typing_inv in Htype as [ts [Hts _]] => //.
    destruct ts; by inversion Hts.
  (* term_SEQ *)
  - apply (term_SEQ_typing_inv (term_SEQ t1 t2) _ _ _ _ eq_refl) in Htype
    as [ts [Htype1 Htype2]].
    apply t. (* TODO just doing identity for now *)
Defined.

Recursive Extraction interpret_one_step.
