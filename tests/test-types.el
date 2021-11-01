;; -*- lexical-binding: t -*-

(require 'elsa-undercover)
(require 'elsa-types)

(require 'elsa-test-helpers)

(describe "Elsa Types"


  (describe "Make type"

    (it "should make a simple type"
      (let ((type (elsa-make-type string)))
        (expect (elsa-type-string-p type) :to-be-truthy)
        (expect (elsa-type-nullable-p type) :not :to-be-truthy)))

    (it "should make a simple nullable type"
      (let ((type (elsa-make-type (or string nil))))
        (expect (elsa-sum-type-p type) :to-be-truthy)
        (expect (elsa-type-accept type (elsa-make-type string)) :to-be-truthy)
        (expect (elsa-type-nullable-p type) :to-be-truthy)))

    (it "should not make unknown type"
      (expect (elsa-make-type ratherimporbablenameofatype) :to-throw))

    (it "should make a sum type from a sum definition"
      (let ((type (elsa-make-type (or string int))))
        (expect (elsa-sum-type-p type) :to-be-truthy)
        (expect (elsa-type-accept type (elsa-make-type string)) :to-be-truthy)
        (expect (elsa-type-accept type (elsa-make-type int)) :to-be-truthy)
        (expect (elsa-type-accept type (elsa-make-type float)) :not :to-be-truthy))))


  (describe "Test type hierarchy"


    (it "should recognize subtypes reflexively"
      (expect (elsa-instance-of (elsa-make-type int) (elsa-make-type int))))

    (it "should recognize proper subtypes"
      (expect (elsa-instance-of (elsa-make-type int) 'number)))


    (describe "Work with instances or types"


      (it "should compare two types directly"
        (expect (elsa-instance-of 'int 'number)))

      (it "should compare an instance and a type"
        (expect (elsa-instance-of (elsa-make-type int) 'number)))

      (it "should compare two instances"
        (expect (elsa-instance-of (elsa-make-type int) (elsa-make-type int))))))


  (describe "Cons type"

    (it "of mixed should accept any cons"
      (expect (elsa-type-accept
               (elsa-make-type (cons mixed mixed))
               (elsa-make-type (cons int string)))
              :to-be-truthy))

    (it "should be covariant in first type argument"
      (expect (elsa-type-accept
               (elsa-make-type (cons number string))
               (elsa-make-type (cons int string)))
              :to-be-truthy))

    (it "should be covariant in second type argument"
      (expect (elsa-type-accept
               (elsa-make-type (cons string number))
               (elsa-make-type (cons string int)))
              :to-be-truthy))

    (it "of should not accept if any of types is not a subtype of the other"
      (expect (elsa-type-accept
               (elsa-make-type (cons number string))
               (elsa-make-type (cons string int)))
              :not :to-be-truthy))

    (it "of should not accept if any of types is not a subtype of the other"
      (expect (elsa-type-accept
               (elsa-make-type (cons string number))
               (elsa-make-type (cons int string)))
              :not :to-be-truthy)))


  (describe "Sum type"

    (it "should not share data with its clone"
      (let* ((old (elsa-make-type (or int string)))
             (new (clone old)))
        (expect (eq old new) :not :to-be-truthy)
        (expect (eq (car (oref old types))
                    (car (oref new types))) :not :to-be-truthy)
        (oset new types nil)
        (expect (length (oref old types)) :to-be 2)
        (expect (length (oref new types)) :to-be 0)))

    (it "should be able to hold no types"
      (let ((sum (elsa-sum-type)))
        (expect (length (oref sum types)) :to-equal 0)))

    (it "should accept nothing if empty"
      (let ((sum (elsa-sum-type)))
        (expect (elsa-type-accept sum (elsa-make-type mixed)) :not :to-be-truthy)
        (expect (elsa-type-accept sum (elsa-make-type int)) :not :to-be-truthy)
        (expect (elsa-type-accept sum (elsa-sum-type)) :not :to-be-truthy)))

    (it "should be able to hold more types"
      (let ((sum (elsa-type-sum (elsa-make-type int) (elsa-make-type string))))
        (expect (length (oref sum types)) :to-equal 2)))

    (it "should accept a type if it is accepted by at least one type of the sum"
      (let ((sum (elsa-type-sum (elsa-make-type int) (elsa-make-type string))))
        (expect (elsa-type-accept sum (elsa-make-type int)) :to-be-truthy)))

    (it "should accept nil type if nullable"
      (let ((sum (elsa-type-sum (elsa-make-type nil) (elsa-make-type string))))
        (expect (elsa-type-accept sum (elsa-make-type nil)) :to-be-truthy)))

    (it "should accept nil type if it holds just nil"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type nil)))
        (expect (elsa-type-accept sum (elsa-make-type nil)) :to-be-truthy)))

    (it "should accept a type if it is accepted by at least one nullable type of the sum"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type (or int nil))))
        (setq sum (elsa-type-sum sum (elsa-make-type string)))
        (expect (elsa-type-accept sum (elsa-make-type int)) :to-be-truthy)))

    (it "should not accept a nullable type if it is not accepted by the same nullable type int the sum"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type string)))
        (expect (elsa-type-accept sum (elsa-make-type (or int nil))) :not :to-be-truthy)))

    (it "should not accept a type if it is not accepted by at least one type of the sum"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type string)))
        (expect (elsa-type-accept sum (elsa-make-type float)) :not :to-be-truthy)))

    (it "should be nullable if some type in the sum is nullable"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type (or string nil))))
        (expect (elsa-type-nullable-p sum) :to-be-truthy)))

    (it "should be nullable if nil type is added"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type nil)))
        (expect (elsa-type-nullable-p sum) :to-be-truthy)))

    (it "should accept a sum type which is a subset of itself"
      (let ((sumA (elsa-sum-type))
            (sumB (elsa-sum-type)))
        (setq sumA (elsa-type-sum sumA (elsa-make-type string)))
        (setq sumA (elsa-type-sum sumA (elsa-make-type int)))
        (setq sumA (elsa-type-sum sumA (elsa-make-type float)))
        (setq sumB (elsa-type-sum sumB (elsa-make-type string)))
        (setq sumB (elsa-type-sum sumB (elsa-make-type int)))
        (expect (elsa-type-accept sumA sumB) :to-be-truthy)))

    (it "should not accept a sum type which is not a subset of itself"
      (let ((sumA (elsa-sum-type))
            (sumB (elsa-sum-type)))
        (setq sumA (elsa-type-sum sumA (elsa-make-type string)))
        (setq sumA (elsa-type-sum sumA (elsa-make-type int)))
        (setq sumB (elsa-type-sum sumB (elsa-make-type float)))
        (setq sumB (elsa-type-sum sumB (elsa-make-type string)))
        (setq sumB (elsa-type-sum sumB (elsa-make-type int)))
        (expect (elsa-type-accept sumA sumB) :not :to-be-truthy))))


  (describe "Diff type"

    (it "should not accept types where the positive does not accept the other type"
      (expect (elsa-diff-type :positive (elsa-type-int))
              :not :to-accept-type (elsa-type-keyword)))

    (it "should not accept types where the negative is accepted by the other type"
      (expect (elsa-diff-type :negative (elsa-type-int))
              :not :to-accept-type (elsa-type-number))))


  (describe "Mixed type"


    (it "should accept any proper type"
      (expect (elsa-type-accept (elsa-make-type mixed)
                                (elsa-make-type string))
              :to-be-truthy))

    (it "should accept nullable types by default"
      (expect (elsa-type-accept (elsa-make-type mixed)
                                (elsa-make-type (or string nil)))
              :to-be-truthy))

    (xit "should not accept nullable if it was made non-nullable"
      (let ((instance (elsa-make-type mixed)))
        (elsa-type-make-non-nullable instance)
        (expect (elsa-type-accept instance (elsa-make-type (or string nil)))
                :not :to-be-truthy)))

    (xit "should accept non-nullable if it was made non-nullable"
      (let ((instance (elsa-make-type mixed)))
        (elsa-type-make-non-nullable instance)
        (expect (elsa-type-accept instance (elsa-make-type string))
                :to-be-truthy)))

    (it "should not accept unbound type"
      (expect (elsa-type-accept (elsa-make-type mixed)
                                (elsa-make-type unbound))
              :not :to-be-truthy))

    (it "is always created as nullable"
      (expect (elsa-type-nullable-p (elsa-make-type mixed))
              :to-be-truthy))

    (xit "can be made non-nil"
      (let ((instance (elsa-make-type mixed)))
        (elsa-type-make-non-nullable instance)
        (expect (elsa-type-nullable-p instance) :not :to-be-truthy))))


  (describe "Simple type"


    (it "should not be changed by being made non-nullable"
      (expect (elsa-type-make-non-nullable (elsa-make-type string)) :to-equal (elsa-make-type string)))

    (it "should not share data with its clone"
      (let* ((old (elsa-make-type int))
             (new (clone old)))
        (expect (eq old new) :not :to-be-truthy))))

  (describe "Bool type"

    (it "should accept t"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-type-t)) :to-be-truthy))

    (it "should accept nil"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-type-t)) :to-be-truthy))

    (it "should accept t?"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-make-type bool)) :to-be-truthy))

    (it "should accept bool"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-type-bool)) :to-be-truthy))

    (it "should not accept int|bool"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-make-type (or int bool))) :not :to-be-truthy))

    (it "should not accept int|t"
      (expect (elsa-type-accept (elsa-type-bool) (elsa-make-type (or int t))) :not :to-be-truthy)))

  (describe "Just-nullable type"


    (it "should accept nil if nullable"
      (expect (elsa-type-accept (elsa-make-type (or string nil))
                                (elsa-make-type nil))
              :to-be-truthy))

    (it "should not accept nil if not nullable"
      (expect (elsa-type-accept (elsa-make-type string)
                                (elsa-make-type nil))
              :not :to-be-truthy))

    (it "should accept non-nullable types if it is nullable"
      (expect (elsa-type-accept (elsa-make-type (or string nil))
                                (elsa-make-type string))
              :to-be-truthy))

    (it "should not accept nullable types if it is non-nullable"
      (expect (elsa-type-accept (elsa-make-type string)
                                (elsa-make-type (or string nil)))
              :not :to-be-truthy))

    (it "should accept subtypes"
      (expect (elsa-type-accept (elsa-make-type number)
                                (elsa-make-type int))
              :to-be-truthy))

    (it "should not accept supertypes"
      (expect (elsa-type-accept (elsa-make-type int)
                                (elsa-make-type number))
              :not :to-be-truthy))

    (it "should accept sum type if it accepts every type of the sum"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type float)))
        (expect (elsa-type-accept (elsa-make-type number) sum) :to-be-truthy)))

    (it "should not accept sum type if it can not accept some type of the sum"
      (let ((sum (elsa-sum-type)))
        (setq sum (elsa-type-sum sum (elsa-make-type int)))
        (setq sum (elsa-type-sum sum (elsa-make-type string)))
        (expect
         (elsa-type-accept (elsa-make-type number) sum) :not :to-be-truthy)))))
