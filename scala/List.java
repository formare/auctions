import java.util.Scanner;


/** 
 * @author Uday Reddy, with changes by Manfred Kerber
 * @version 2014-12-03 based on Uday's version of 2012
 * 
 * List class defines a recursive type called List, and provides
 * constructor and getter methods. 
 */

public class List {

    private boolean empty;
    private int head;
    private List tail;

    /**
     * The first constructor creates a list consisting of a head, that is,
     * an integer and a tail, which is another list of integers.
     * @param head
     * @param tail
     */
    public List(int head, List tail) {
        this.empty = false; 
        this.head = head;
        this.tail = tail;
    }

    /**
     *  The second constructor creates an empty list, i.e., a list with no elements.
     *  For this list, head and tail remain undefined, calls to the corresponding getters
     *  will have to result in an exception.
     */
    public List() {
        this.empty = true;
    }

    /**
     * Creates a new list from a given head element and a tail List
     */
    public static List cons(int head, List tail) {
        return new List(head,tail);
    }

    /**
     * Creates a new empty List
     */
    public static List empty() {
        return new List();
    }

    public boolean getEmpty() {
        return this.empty;
    }


    public String toString() {
        return "[" + toStringAux() + "]";
    }


    public String toStringAux() {
        if (getEmpty()) {
            return "";
        } else if (getTail().isEmpty()){
            return getHead() + "";
        } else {
            return getHead() + ", " + getTail().toStringAux();
        }
    }


    /**
     * 
     * @param l1 first list
     * @param l2 second list
     * @return true iff the two lists are equal
     */
    public static boolean equals(List l1, List l2) {
        if (l1.isEmpty() && l2.isEmpty()) {
            return true;
        } else if (l1.isEmpty() || l2.isEmpty()) {
            return false;
        } else if (l1.getHead() == l2.getHead()) {
            return equals(l1.getTail(), l2.getTail());
        } else {
            return false;
        }
    }


    /**
     * returns true if this list is empty
     */
    public boolean isEmpty() {
        return empty;
    }

    /**
     * returns the head of this list or throws an exception if the
     * list is empty
     * @throws IllegalStateException if the list is empty
     */
    public int getHead() {
        if (isEmpty()) {
            throw new IllegalStateException(
                                            "Trying to access head of an empty list");
        }
        return head;
    }

    /**
     * returns the tail of this list or throws an exception if the
     * list is empty
     * @throws IllegalStateException if the list is empty
     */    
    public List getTail() {
        if (isEmpty()) {
            throw new IllegalStateException(
                                            "Trying to access tail of an empty list");
        }
        return tail;
    }

    public void setEmpty(boolean empty) {
        this.empty = empty;
    }

    public void setHead(int head) {
        this.head = head;
    }

    public void setTail(List tail) {
        this.tail = tail;
    }

    /**
     *   Note that the argument list in the following (int... inputs)
     *   reads any number of arguments into an array inputs of type int[]
     */
    public static List makeList(int... inputs) {
        List result = new List();
        for (int i = 0; i < inputs.length; i++) {
            result = new List(inputs[i], result);
        }
        return result;
    }

    public static int select(int n, List a) {
        if (a.isEmpty())
            throw new IllegalStateException(
                                            "select - list does not have enough elements.");
        else if (n == 0)
            return a.getHead();
        else
            return select(n-1, a.getTail());
    }

    /**
     * Return the last element of list a.  Assume that theres is an element.
     */
    public static int last(List a) {
        if (a.isEmpty())
            throw new IllegalStateException("list does not have any elements.");
        else if (a.getTail().isEmpty())
            return a.getHead();
        else
            return last(a.getTail());
    }
        
    public static List lastListElement(List a) {
        if (a.isEmpty())
            throw new IllegalStateException("list does not have any elements.");
        else if (a.getTail().isEmpty())
            return a;
        else
            return lastListElement(a.getTail());
    }
        
    public static int min(List list) {
        if (list.isEmpty())
            throw new IllegalStateException("list does not have "
                                            + "any elements.");
        else if (list.getTail().isEmpty()) {
            return list.getHead();
        } else {
            return Math.min(list.getHead(), min(list.getTail()));
        }
    }


    /**
     * Add an element x to the end of a list a.
     * Return the extended list.
     */

    public static List addToEnd(List a, int x) {
        if (a.isEmpty()) {
            return cons(x, empty());
        } else {
            return cons(a.getHead(), addToEnd(a.getTail(), x));
        }
    }

    /**
     * Creates a List which is the result of List b appended to the
     * end of List a
     */
    public static List append(List a, List b) {
        if (a.isEmpty()) {
            return b;
        } else {
            return cons(a.getHead(), append(a.getTail(), b));
        }
    }

    /**
     * addToEnd can also be defined using append without any further recursion.

     public static List addToEnd(List a, int x) {
     return append(a, cons(x, empty()));
     }

    */

    /**
     * A naive implementation of reversing a List. Can take quite long
     * on large lists
     */
    public static List naiveReverse(List a) {
        if (a.isEmpty()) {
            return empty();
        } else {
            return addToEnd(naiveReverse(a.getTail()), a.getHead());
        }
    }

    /**
     * An efficient (tail recursive) implementation to reverse a List 
     * that uses a helper method and an accumulator
     */
    public static List reverse(List list) {
        return reverseAccumulate(list, empty());
    }

    private static List reverseAccumulate(List original, List reversed) {
        if (original.isEmpty()) {
            return reversed;
        } else {
            return reverseAccumulate(original.getTail(), 
                                     cons(original.getHead(), reversed));
        }
    }

    public static int length(List l) {
        if (l.isEmpty()) {
            return 0;
        } else {
            return 1 + length(l.getTail());
        }
    }
                
    public static List remove(int position, List l) {
        if (l.isEmpty()) {
            throw new IllegalStateException(
                                            "remove - list does not have enough elements.");
        }
        else if (position == 0) {
            return l.getTail();
        }
        else {
            return new List(l.getHead(), remove(position-1, l.getTail()));
        }
    }


    ////////////////////////////////////////////////////////////////////////////////////////

    public static boolean alive(List l) {
        return (l.isEmpty() || l.getTail().isEmpty() 
                || l.getHead() != l.getTail().getHead());
    }

    public static int giveValue(int i) {
        Scanner s = new Scanner(System.in);
        return s.nextInt();
    }

    public static List addToList(List l) {
        int value;
        if (alive(l)) {
            value = giveValue(length(l));
            l = cons(value, l);
            System.out.println("l: " + l);
            return addToList(l);
        } else {
            System.out.println("Price to pay: " + l.getHead());
            return l;
        }
    }
 
    public static void main(String[] args) {
        addToList(empty());
    }
}
