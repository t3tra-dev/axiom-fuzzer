(* Known hole in the output: "uu relies on an unsafe hierarchy." *)
Unset Universe Checking.
Definition U := Type.
Definition uu : U := U.
Set Universe Checking.
Print Assumptions uu.
