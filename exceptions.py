class InvalidArrayRange(Exception):
    def __init__(self, lnumber, a, b, message="Error"):
        self.message = ("Błąd (linia %s): Nieprawidłowy zakres tablicy: (a:b) = (%s:%s)" % (lnumber, a, b))
        super().__init__(self.message)

class NotDeclared(Exception):
    def __init__(self, word,  lnumber=None, message="Error"):
        lnumber = f' (linia {lnumber})' if lnumber else ''
        self.message = ("Błąd%s: Niezadeklarowana zmienna: %s" % (lnumber, word))
        super().__init__(self.message)

class AlreadyDeclared(Exception):
    def __init__(self,  name, lnumber=None, message="Error"):
        lnumber = f' (linia {lnumber})' if lnumber else ''
        self.message = ("Błąd%s: Zmienna uprzednio zadeklarowana: %s" % (lnumber, name))
        super().__init__(self.message)

class NotAnArray(Exception):
    def __init__(self, lnumber, name, message="Error"):
        self.message = ("Błąd (linia %s): odwołanie się do zmiennej jak do tablicy: %s" % (lnumber, name))
        super().__init__(self.message)

class NotAVariable(Exception):
    def __init__(self, lnumber, name, message="Error"):
        self.message = ("Błąd (linia %s): odwołanie się do tablicy jak do zmiennej: %s" % (lnumber, name))
        super().__init__(self.message)

class IteratorModification(Exception):
    def __init__(self, name, message="Error"):
        self.message = ("Błąd: modyfikacja iteratora %s w trakcie pętli" % (name))
        super().__init__(self.message)

class NotInitialized(Exception):
    def __init__(self, name, lnumber=None, message="Error"):
        lnumber = f' (linia {lnumber})' if lnumber else ''
        self.message = ("Błąd%s: Niezainicjalizowana zmienna: %s" % (lnumber, name))
        super().__init__(self.message)

class ReusedIterator(Exception):
    def __init__(self, name, message="Error"):
        self.message = ("Błąd, ponowne użycie iteratora %s" % name)
        super().__init__(self.message)

class InvalidArrayElement(Exception):
    def __init__(self, lnumber, index, name, message="Error"):
        self.message = ("Błąd (linia %s): Indeks %s w tablicy %s nie istnieje  " % (lnumber, index,name))
        super().__init__(self.message)

class InvalidCharacter(Exception):
    def __init__(self, lnumber, character, message="Error"):
        self.message = ("Błąd (linia %s): Nieprawidłowy zapis %s" % (lnumber, character))
        super().__init__(self.message)