(set-info :status unknown)
(set-option :produce-models true)
(set-logic AUFLIRA)
; Declare a function taking a round, match, slot, and returns an integer
; indicating which team is at that slot.
(declare-fun sparticus (Int Int Int) Int)
; Parameterise some things
(define-fun team_count () Int 12)
(define-fun round_limit () Int 3)
(define-fun match_limit () Int 3)

; Assert that for all slots, the outcome is in range.
(assert (forall ((round Int) (match Int) (slot Int))
  (and
    (>= (sparticus round match slot) 0)
    (< (sparticus round match slot) team_count))))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round Int) (match Int) (slota Int) (slotb Int))
  (or (or (> round round_limit) (< round 0))
  (or (or (> match match_limit) (< match 0))
  (or (or (> slota 4) (< slota 0))
  (or (or (> slotb 4) (< slotb 0))
  ; Check they're not the same slot
  (or (= slota slotb)
  ; Ensure they're distinct otherwise
  (distinct (sparticus round match slota) (sparticus round match slotb)))))))))
(check-sat)
;(get-model)
