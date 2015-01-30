import java.util.Scanner;


/** 
 * @author Uday Reddy, with changes by Manfred Kerber
 * @version 2014-12-03 based on Uday's version of 2012
 * 
 * List class defines a recursive type called List, and provides
 * constructor and getter methods. 
 */

public class Matrix {
    private int rows;
    private boolean empty;
    private List head;
    private Matrix tail;

    /**
     * The first constructor creates a list consisting of a head, that is,
     * an integer and a tail, which is another list of integers.
     * @param head
     * @param tail
     */
    public Matrix(int n, List head, Matrix tail) {
        this.rows = n;
        this.empty = false; 
        this.head = head;
        this.tail = tail;
    }

    /**
     *  The second constructor creates an empty list, i.e., a list with no elements.
     *  For this list, head and tail remain undefined, calls to the corresponding getters
     *  will have to result in an exception.
     */
    public Matrix(int n) {
        this.rows = n;
        this.empty = true;
    }

    /**
     * Creates a new list from a given head element and a tail List
     */
    public static Matrix cons(List head, Matrix tail) {
        return new Matrix(head,tail);
    }

    /**
     * Creates a new empty List
     */
    public static Matrix empty(int n) {
        return new Matrix(n);

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
    public static boolean equals(Matrix l1, Matrix l2) {
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
    public List getHead() {
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
    public Matrix getTail() {
        if (isEmpty()) {
            throw new IllegalStateException(
                                            "Trying to access tail of an empty list");
        }
        return tail;
    }

    public static int length(Matrix l) {
        if (l.isEmpty()) {
            return 0;
        } else {
            return 1 + length(l.getTail());
        }
    }
                

    ////////////////////////////////////////////////////////////////////////////////////////

    // need to implement matrix and equals on vectors

    private static Scanner s = new Scanner(System.in);

    public static boolean alive(Matrix m) {
        return (m.isEmpty() || m.getTail().isEmpty() 
                || ! m.getHead().equals(m.getTail().getHead()));
    }

    public static Matrix giveValue(int cols, int rows) {
        if (rows == 0) {
            return empty(); 
        } else {
            return cons(s.nextInt(), giveValue(cols, rows - 1));
        }
    }

    public static Matrix addToMatrix(Matrix m) {
        int value;
        if (alive(m)) {
            value = giveValue(cols(m),rows(m));
            m = cons(value, m);
            System.out.println("m: " + m);
            return addToMatrix(m);
        } else {
            System.out.println("Winner: "       + m.wdp());
            System.out.println("Price to pay: " + m.price());
            return m;
        }
    }
 
    public static void main(String[] args) {
        System.out.println("Enter the number of bidders.");
        int bidders = s.nextInt();
        addToMatrix(empty(bidders));
    }
}
