(load "pmatch.scm")

(define-syntax output 
  (syntax-rules (unquote)
    ((_ (unquote g) t t* ...)
     (format "~a ~a"
             g 
             (output t t* ...)))
    ((_ (unquote t))
     (format "~a" t))
    ((_ t0 t1 t* ...)
     (format "~a ~a"
             `t0 (output t1 t* ...)))
    ((_ (t ...))
     (format "(~a)"
             (output t ...)))
    ((_ t)
     (format "~a" `t))))

;; We use printf so that we can output quoted things
(define (to-feldspar x) (printf (help->feldspar x '())))

(define typ-sym
  (lambda (typ)
    (string->symbol (format "GADT.~a" typ))))

(define help->feldspar
 (lambda(ls env)
   (define lax 
    (lambda(var env)
     (if (eq? var (car env)) 'GADT.Zro `(GADT.Suc ,(lax var (cdr env))))))
  (pmatch ls
    [,x (guard(number? x)) (output (GADT.Con ,x))]
    [,y ( guard(and (symbol? y) (member y env))) (output (GADT.Var ,(lax y env)))]
    [(add1 ,b) (output (GADT.Add (GADT.Con 1) ,(help->feldspar b env)))]
    [(* ,e1 ,e2) (output (GADT.Mul ,(help->feldspar e1 env) ,(help->feldspar e2 env)))]
    [(+ ,e1 ,e2) (output (GADT.Add ,(help->feldspar e1 env) ,(help->feldspar e2 env)))]
    [(lambda(,x : ,typ) ,body) (output (GADT.Abs ,(typ-sym typ) ,(help->feldspar body (cons x env)))) ]
    [(,t ,h) (output (GADT.App ,(help->feldspar t env) ,(help->feldspar h env)))])))
