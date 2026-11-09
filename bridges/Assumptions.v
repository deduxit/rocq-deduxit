(* linlog © Fabian Lukas Grubmüller 2026 *)
(* Licensed under the EUPL *)

(** What the bridges rest on: nothing beyond the definitions of the two
    sides. Rocq answers "Closed under the global context" for each,
    which the flake's check requires. *)

From Deduxit.Linear.Bridges Require NanoYallaBridge NanoIllBridge.

Print Assumptions Deduxit.Linear.Bridges.NanoYallaBridge.ll_iff_nanoll.
Print Assumptions Deduxit.Linear.Bridges.NanoYallaBridge.nanoll_iff_ll.
Print Assumptions Deduxit.Linear.Bridges.NanoIllBridge.ill_iff_nanoill.
Print Assumptions Deduxit.Linear.Bridges.NanoIllBridge.nanoill_iff_ill.
