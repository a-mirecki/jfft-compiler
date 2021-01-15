class InvalidArrayRange(Exception):
    def __init__(self, lnumber, a, b, message="Error"):
        self.message = ("Błąd w linijce %s, nieprawidlowy zakres tablicy: (a:b) = (%s:%s)" % (lnumber, a, b))
        super().__init__(self.message)

class BadKeyword(Exception):
    def __init__(self, lnumber, word, message="Error"):
        self.message = ("Błąd w linijce %s, nieprawidlowe słowo kontrolne: %s" % (lnumber, word))
        super().__init__(self.message)

class NotDeclared(Exception):
    def __init__(self, lnumber, word, message="Error"):
        self.message = ("Błąd w linijce %s, zmienna nie zadeklarowana: %s" % (lnumber, word))
        super().__init__(self.message)

class AlreadyDeclared(Exception):
    def __init__(self, lnumber, name, message="Error"):
        self.message = ("Błąd w linijce %s, zmienna uprzednio zadeklarowana: %s" % (lnumber, name))
        super().__init__(self.message)

class NotAnArray(Exception):
    def __init__(self, lnumber, name, message="Error"):
        self.message = ("Błąd w linijce %s, odwołanie się do zmiennej jak do tablicy: %s" % (lnumber, name))
        super().__init__(self.message)

class NotAVariable(Exception):
    def __init__(self, lnumber, name, message="Error"):
        self.message = ("Błąd w linijce %s, odwołanie się do tablicy jak do zmiennej: %s" % (lnumber, name))
        super().__init__(self.message)

class IteratorModification(Exception):
    def __init__(self, name, message="Error"):
        self.message = ("Błąd, modyfikacja iteratora  %s w trakcie pętli" % (name))
        super().__init__(self.message)

class NotInitialized(Exception):
    def __init__(self, name, message="Error"):
        self.message = ("Błąd, zmienna nie zainicjalizowana: %s" % name)
        super().__init__(self.message)

class ReusedIterator(Exception):
    def __init__(self, name, message="Error"):
        self.message = ("Błąd, ponowne użycie iteratora %s" % name)
        super().__init__(self.message)