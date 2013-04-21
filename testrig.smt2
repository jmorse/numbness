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
(define-fun teams_per_round () Int 4)

; Assert that for all slots, the outcome is in range.
(assert (forall ((round Int) (match Int) (slot Int))
  (and
    (>= (sparticus round match slot) 0)
    (< (sparticus round match slot) team_count))))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round Int) (matcha Int) (matchb Int) (slota Int) (slotb Int))
  (or (or (> round round_limit) (< round 0))
  (or (or (> matcha match_limit) (< matcha 0))
  (or (or (> matchb match_limit) (< matchb 0))
  (or (or (> slota teams_per_round) (< slota 0))
  (or (or (> slotb teams_per_round) (< slotb 0))
  ; Check they're not the same slot or match
  (or (= slota slotb)
  (or (= matcha matchb)
  ; Ensure they're distinct otherwise
  (distinct (sparticus round matcha slota) (sparticus round matchb slotb)
))))))))))
(check-sat)
;(get-model)
