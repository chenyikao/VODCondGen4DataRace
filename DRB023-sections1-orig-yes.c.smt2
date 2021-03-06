

(declare-sort Char)
(define-sort Str () (Array Int Char))
(echo "Simulating signed 128 bit number domain...")
(echo "(including GNU C int128 (2's complement) and IEEE 754 binary128 overflow but excluding underflow)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/Integers-implementation.html#Integers-implementation)")
(echo "(https://gcc.gnu.org/onlinedocs/gcc/_005f_005fint128.html#g_t_005f_005fint128)")
(echo "(https://en.wikipedia.org/wiki/Quadruple-precision_floating-point_format#IEEE_754_quadruple-precision_binary_floating-point_format:_binary128)")
(define-fun MAX_MAX_INT () Int 9223372036854775807)  ;RangeDegradeMAX
(declare-fun MAX_INT () Int)                  ;RangeDegradeParam
(define-fun MIN_MAX_INT () Int 0)                     ;RangeDegradeMIN
(define-fun MIN_INT () Int (- (- MAX_INT) 1))
(define-fun MAX_REAL () Real (* (^ 2.0 1023) (- 2.0 (^ 2.0 (- 52)))))
(define-fun MIN_REAL () Real (- MAX_REAL))
;avoiding +/-/*/division/modulo overflow
(define-fun add_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (+ _1 _2))(<= (+ _1 _2) MAX_INT)
	))
(define-fun sub_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (- _1 _2))(<= (- _1 _2) MAX_INT)
))
(define-fun mul_guard ((_1 Int)(_2 Int)) Bool (and 
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
	(<= MIN_INT (* _1 _2))(<= (* _1 _2) MAX_INT)
))
(define-fun div_guard ((_1 Int)(_2 Int)) Bool (and 
	(not (= _2 0))
	(<= MIN_INT _1)(<= _1 MAX_INT)
	(<= MIN_INT _2)(<= _2 MAX_INT)
))
(define-fun mod_guard ((_1 Int)(_2 Int)) Bool (and 
	(div_guard _1 _2)
))
(declare-fun _t_56_DRB023-sections1-orig-yes_c_FUNCTION__t_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun _chunk_size_56_DRB023-sections1-orig-yes_c__chunk_size_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun _chunk_56_DRB023-sections1-orig-yes_c_THREAD1__chunk_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun _chunk_56_DRB023-sections1-orig-yes_c_THREAD2__chunk_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun _nthreads__nthreads () Int)		;RangeDegradeParam
(declare-fun _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c () Int)
(declare-fun i_60_DRB023-sections1-orig-yes_c () Int)
(define-fun main () Int 0)

(define-fun ParallelCondition () Bool (and 

(and (and (< _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c _nthreads__nthreads) (< 0 _t_56_DRB023-sections1-orig-yes_c_FUNCTION__t_56_DRB023-sections1-orig-yes_c _nthreads__nthreads) (not (= _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c)) (<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c) (not (= _chunk_56_DRB023-sections1-orig-yes_c_THREAD1__chunk_56_DRB023-sections1-orig-yes_c _chunk_56_DRB023-sections1-orig-yes_c_THREAD2__chunk_56_DRB023-sections1-orig-yes_c)) (< _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c _nthreads__nthreads) (<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c)) (<= 0 _chunk_56_DRB023-sections1-orig-yes_c_THREAD1__chunk_56_DRB023-sections1-orig-yes_c MAX_INT) (<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c MAX_INT) (<= 1 _nthreads__nthreads MAX_INT) (<= 0 _chunk_56_DRB023-sections1-orig-yes_c_THREAD2__chunk_56_DRB023-sections1-orig-yes_c MAX_INT) (<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c MAX_INT) (<= 0 _t_56_DRB023-sections1-orig-yes_c_FUNCTION__t_56_DRB023-sections1-orig-yes_c MAX_INT))
(<= 0 _chunk_56_DRB023-sections1-orig-yes_c_THREAD1__chunk_56_DRB023-sections1-orig-yes_c MAX_INT)
(<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD1__t_56_DRB023-sections1-orig-yes_c MAX_INT)
(<= 1 _nthreads__nthreads MAX_INT)
(<= 0 _chunk_56_DRB023-sections1-orig-yes_c_THREAD2__chunk_56_DRB023-sections1-orig-yes_c MAX_INT)
(<= 0 _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c MAX_INT)
(<= 0 _t_56_DRB023-sections1-orig-yes_c_FUNCTION__t_56_DRB023-sections1-orig-yes_c MAX_INT)
))

;_LB,     _1,    _UB
(define-fun InCarryInRange ((_1 Int)(_LB Int)(_UB Int)) Bool (and
  (<= _LB _1)(<= _1 _UB)
))
(define-fun InCarryInRangeUB ((_1 Int)(_UB Int)) Bool (or
  (= _1 _UB)
  (< _1 _UB)
))
(define-fun InCarryInRangeLB ((_1 Int)(_LB Int)) Bool (or
  (= _1 _LB)
  (> _1 _LB)
))

(echo "Range down-grade...")
;RangeDegradeUB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeUB _1 9223372036854775807))
;RangeDegradeIn(define-fun InRange ((_1 Int)) Bool (InCarryInRange _1 0 9223372036854775807))
;RangeDegradeLB(define-fun InRange ((_1 Int)) Bool (InCarryInRangeLB _1 0))
;RangeDegradeParams(assert (InRange _nthreads__nthreads))

(assert ParallelCondition)

(assert (= i_60_DRB023-sections1-orig-yes_c 2))
(assert (<= MIN_INT _t_56_DRB023-sections1-orig-yes_c_THREAD2__t_56_DRB023-sections1-orig-yes_c MAX_INT))
(assert (<= MIN_INT i_60_DRB023-sections1-orig-yes_c MAX_INT))

(check-sat)
(get-model)
(exit)