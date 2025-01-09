Require Import Automation.

Section prefixTrace.

  Context {Point : Type}{Link : Point -> Point -> Type}.

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

  Inductive suffixTrace : Point -> Point -> Type :=
  | sclnil : forall {p}, suffixTrace p p
  | ssnoc : forall {from mid to},
    suffixTrace from mid -> Link mid to -> suffixTrace from to.

  Fixpoint suffix_app
            {from mid to}
            (xs : suffixTrace from mid)
            (ys : suffixTrace mid to) : suffixTrace from to :=
    match ys with
    | sclnil => fun xs => xs
    | ssnoc ys' y => fun xs => ssnoc (suffix_app xs ys') y
    end xs.

  Fixpoint pt_to_st {from to} (st : suffixTrace from to) : prefixTrace from to :=
    match st with
    | sclnil => tclnil
    | ssnoc st' l =>
        let pt1 := pt_to_st st' in
        let pt2 := tsnoc l tclnil in
        prefix_app pt1 pt2
    end.


  Lemma aux_correct: forall {from to},
    suffixTrace from to -> prefixTrace from to.
  Proof.
    intros from to st.
    now apply pt_to_st.
  Defined.
  

  

End prefixTrace.

