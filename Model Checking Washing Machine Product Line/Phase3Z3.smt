;---------Features--------
(declare-const delay Bool)
(declare-const heat Bool)
(declare-const dry Bool)

;---------States----------
(declare-const locking Bool)
(declare-const waiting Bool)
(declare-const washing Bool)
(declare-const drying Bool)
(declare-const unlocking Bool)
(declare-const EntryTemp Bool)

;----------Transitions-----
(declare-const startP Bool)
(declare-const startW Bool)
(declare-const endP Bool)
(declare-const startD Bool)
(declare-const endD Bool)
(declare-const endW Bool)

;----------Encoding of Feature Model
(define-fun FofW () Bool
    (and 
        (or 
            (or delay heat) 
            dry) 
        (not (and delay heat))
        )
)

(assert FofW)

;-----------Encoding of Domain Model
(define-fun startPrewash () Bool
    (=>
        startP
        (and locking waiting)
    )
)

(define-fun endPrewash () Bool
    (=>
        endP
        (and waiting washing)
    )
)

(define-fun startWash () Bool
    (=>
        startW
        (and locking washing)
    )
)

(define-fun EntryTempCheck () Bool
    (=> EntryTemp washing)
)

(define-fun startDrying () Bool
    (=>
        startD
        (and washing drying)
    )
)

(define-fun endDrying () Bool
    (=>
        endD
        (and drying unlocking)
    )
)

(define-fun endWash () Bool
    (=>
        endW
        (and washing unlocking)
    )
)

;--------Encoding of the Presence Conditions

(define-fun HoDCons () Bool
    (=>
        (or
            (or startP endP)
            waiting
        )
        (or heat delay)    
    )
)

(define-fun HCons () Bool
    (=> EntryTempCheck heat)
)

(define-fun DCons () Bool 
    (=> 
        (or 
            (or startD endD)
            drying    
        )
        dry
    )
)


;------------ Combining F, D and C to verify if it is staisfiable

(define-fun edges () Bool
    (and
        (and 
            (and startPrewash endPrewash)
            (and startWash startDrying)
        )
        (and 
            (and endWash endDrying)
            EntryTempCheck
        )
    )
)

(assert edges)
(assert HoDCons)
(assert HCons)
(assert DCons)

;-------------- For Part 3
(define-fun Heat () Bool
    ;not
    (and
        (and startP endP)
        (and waiting EntryTemp)
    )
)

(define-fun Delay () Bool
    ;not
    (and
        (and startP endP)
        waiting
    )
)

(define-fun Dry () Bool
    ;not
        (and 
            (and startD endD)
            drying
        )
)

(assert Heat)
(assert Delay)
(assert Dry)
(check-sat)
(get-model)
;(define-fun startPrewash () Bool
;    (and l w)
;)

;(define-fun endPreWash () Bool
;    (and w wa)
;)

;(define-fun startWash () Bool
;    (and l wa)
;)
;(define-fun EntryTempCheck () Bool

;)
;(assert startWash)

;(define-fun test () Bool
 ;   (and 
 ;       sP 
 ;       (and 
 ;           l
 ;           (not w)
 ;       )
 ;   )
;)

;(define-fun regularWash() Bool
;    (and
 ;       (and locking washing)
;        unlocking
;    )
;)


;(define-fun Waitingcons () Bool 
;    (=>
;        sW
;        (not w)
;    )
;)

;(define-fun Dryingcons () Bool
;    (=>
;        eW
;        (not dr)
;    )
;)

;(define-fun DofW () Bool
 ;   (and
  ;      (and 
   ;         (and locking washing)
    ;        unlocking
     ;   )
      ;  (and 
       ;     (or 
        ;        startW
         ;       (and startP endP)
          ;  ) 
           ; (or
            ;    endW
             ;   (and startD endD)
            ;)
        ;)
    ;)
;)