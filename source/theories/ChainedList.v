(* This file implements a 'chained list'. This can essentially be
thought of as the proof-relevant transitive reflexive closure of
a relation. That is, each link (element) has a "from" point that
must match the previous element's "to" point. *)
Require Import Automation.
From Coq Require Import List.
Import ListNotations.
Section ChainedList.
(* ChainStep实例化 *)
Context {Point : Type} {Link : Point -> Point -> Type}.

Inductive ChainedList : Point -> Point -> Type :=
  | clnil : forall {p}, ChainedList p p
  | snoc : forall {from mid to},
      ChainedList from mid -> Link mid to -> ChainedList from to.

Fixpoint clist_app
           {from mid to}
           (xs : ChainedList from mid)
           (ys : ChainedList mid to) : ChainedList from to :=
  match ys with
  | clnil => fun xs => xs
  | snoc ys' y => fun xs => snoc (clist_app xs ys') y
  end xs.

  Inductive prefixTrace : Point -> Point -> Type :=
  | tclnil : forall {p}, prefixTrace p p
  | tsnoc : forall {from mid to},
    Link from mid -> prefixTrace mid to -> prefixTrace from to.

  Fixpoint prefix_app {from mid to}
                      (xs : prefixTrace from mid)
                      (ys : prefixTrace mid to) : prefixTrace from to :=
    match xs with
    | tclnil => fun ys => ys
    | tsnoc x xs' => fun ys => tsnoc x (prefix_app xs' ys)
    end ys.

    Fixpoint cl_to_pt {from to} (st : ChainedList from to) : prefixTrace from to :=
    match st with
    | clnil => tclnil
    | snoc st' l =>
        let pt1 := cl_to_pt st' in
        let pt2 := tsnoc l tclnil in
        prefix_app pt1 pt2
    end.

  Fixpoint pt_to_cl {from to} (pt : prefixTrace from to) : ChainedList from to :=
    match pt with
    | tclnil => clnil
    | tsnoc l pt' =>
        let st' := pt_to_cl pt' in                (* st' : suffixTrace mid to *)
        let st'' := snoc clnil l in           (* st'' : suffixTrace from mid *)
        clist_app st'' st'                     (* Combine to get suffixTrace from to *)
    end.

  Lemma cl_to_pt_lm: forall {from to},
    ChainedList from to -> prefixTrace from to.
  Proof.
    intros from to st.
    now apply cl_to_pt.
  Defined.

  Lemma pt_to_cl_lm: forall {from to},
    prefixTrace from to -> ChainedList from to.
  Proof.
    intros from to st.
    now apply pt_to_cl.
  Defined.

Infix "++" := clist_app (right associativity, at level 60).

Definition clist_prefix
           {from mid to}
           (prefix : ChainedList from mid)
           (full : ChainedList from to) : Prop :=
  exists suffix, full = prefix ++ suffix.

Definition clist_suffix
           {from mid to}
           (suffix : ChainedList mid to)
           (full : ChainedList from to) : Prop :=
  exists prefix, full = prefix ++ suffix.

Infix "`prefix_of`" := clist_prefix (at level 70).
Infix "`suffix_of`" := clist_suffix (at level 70).

Fixpoint extract_points {from to : Point} (lst : ChainedList from to) : list Point :=
  match lst with
  | clnil => []  (* 空链表情况：返回空列表 *)
  | snoc sublist link =>
    match sublist with
    | clnil => [to]  (* 只有一个数据点的情况：返回包含该点的列表 *)
    | _ => extract_points sublist ++ [to]  (* 递归处理子链表并添加当前点到列表末尾 *)
    end
  end.



Section Theories.
Lemma app_clnil_l {from to} (xs : ChainedList from to) :
  clnil ++ xs = xs.
Proof. induction xs; auto; cbn; solve_by_rewrite. Qed.

Lemma clist_app_assoc
      {c1 c2 c3 c4}
      (xs : ChainedList c1 c2)
      (ys : ChainedList c2 c3)
      (zs : ChainedList c3 c4) :
  xs ++ ys ++ zs = (xs ++ ys) ++ zs.
Proof. induction zs; intros; auto; cbn; solve_by_rewrite. Qed.
End Theories.

Lemma prefix_of_app
      {from mid to to'}
      {prefix : ChainedList from mid}
      {xs : ChainedList from to}
      {suffix : ChainedList to to'} :
  prefix `prefix_of` xs ->
  prefix `prefix_of` xs ++ suffix.
Proof.
  intros [ex_suffix ex_suffix_eq_app].
  exists (ex_suffix ++ suffix).
  rewrite clist_app_assoc; congruence.
Qed.
End ChainedList.

Declare Scope clist_scope.
Delimit Scope clist_scope with trace.
Bind Scope clist_scope with ChainedList.
Infix "++" := clist_app (right associativity, at level 60) : clist_scope.

Infix "`prefix_of`" := clist_prefix (at level 70) : clist_scope.
Infix "`suffix_of`" := clist_suffix (at level 70) : clist_scope.

Arguments ChainedList : clear implicits.
Arguments prefixTrace : clear implicits.
