(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* --------------------------------------------------------------------- *)
open EcCoreGoal.FApi

val destr_square : EcEnv.env -> EcFol.form ->  EcTypes.memtype * EcFol.form
(* -------------------------------------------------------------------- *)
val t_hoare_of_bdhoareS : backward
val t_hoare_of_bdhoareF : backward
val t_bdhoare_of_hoareS : backward
val t_bdhoare_of_hoareF : backward

val t_hoare_of_muhoareS : backward
val t_hoare_of_muhoareF : backward
