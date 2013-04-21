(set-info :status unknown)
(set-option :produce-models true)
(set-logic AUFBV)

; Declare a function taking a round, match, slot, and returns an integer
; indicating which team is at that slot.
(declare-fun sparticus ((_ BitVec 4) (_ BitVec 4) (_ BitVec 4)) (_ BitVec 4))

; Parameterise some things
; FIXME: when teamcount doesn't fit in BV sort?
(define-fun team_count () (_ BitVec 4) (_ bv12 4))
(define-fun round_limit () (_ BitVec 4) (_ bv6 4))
(define-fun match_limit () (_ BitVec 4) (_ bv3 4))
(define-fun teams_per_round () (_ BitVec 4) (_ bv4 4))

; Assert that for all slots, the outcome is in range.
(assert (forall ((round (_ BitVec 4)) (match (_ BitVec 4)) (slot (_ BitVec 4)))
    (bvult (sparticus round match slot) team_count)))

; Assert that for all matches in a round, all slots are distinct.
(assert (forall ((round (_ BitVec 4)) (matcha (_ BitVec 4)) (matchb (_ BitVec 4)) (slota (_ BitVec 4)) (slotb (_ BitVec 4)))
  (or (bvuge round round_limit)
  (or (bvuge matcha match_limit)
  (or (bvuge matchb match_limit)
  (or (bvuge slota teams_per_round)
  (or (bvuge slotb teams_per_round)
  ; Check they're not the same slot or match
  (or (and (= slota slotb) (= matcha matchb))
  ; Ensure they're distinct otherwise
  (distinct (sparticus round matcha slota) (sparticus round matchb slotb)
)))))))))

(check-sat)
;(get-model)
