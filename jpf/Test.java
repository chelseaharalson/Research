import java.io.PrintWriter;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.DocumentBuilder;
import org.w3c.dom.Document;
import org.w3c.dom.NodeList;
import org.w3c.dom.Node;
import org.w3c.dom.Element;
import java.io.File;
import java.util.*;
import java.util.Scanner;

  public class Test {

    static HashMap<String, Integer> priorityTable = new HashMap<String, Integer>();
    static List list = new ArrayList();

    public static void main(String args[]) throws Exception {
      //int[] array = { 1, 2, 3, 4, 5, 6, 7 };
      /*for (int i = 0; i < array.length; i++) {
        System.out.println("Array Before: " + array[i]);
      }
      System.arraycopy(array, 1, array, 0, array.length - 1);
      for (int i = 0; i < array.length; i++) {
        System.out.println("Array After: " + array[i]);
      }*/

      //array = shiftLeft(array, 1);
      int[] array = { 0, 1, 2, 3, 4, 5, 6 };
      fillPtable(array);

      System.out.println("UNSORTED: " + priorityTable);
      //System.out.println(priorityTable.entrySet());
      //list = new ArrayList(priorityTable.entrySet());
      //System.out.println(list);
      //Collections.sort(list, new Priority(priorityTable));

      //Priority p = new Priority(priorityTable);

      //Collections.sort(list, new Priority(priorityTable));

      System.out.println("SORTED: " + priorityTable);

      /*for (int i = 0; i < priorityTable.size(); i++) {
        System.out.println(priorityTable.get("Test"+i));
      }*/

      /*for (int i = 0; i < array.length; i++) {
        System.out.println("Array Before: " + array[i]);
      }
      array = shiftArray(array, 2);
      for (int i = 0; i < array.length; i++) {
        System.out.println("Array After: " + array[i]);
      }
      System.out.println();
      priorityTable.clear();
      fillPtable(array);*/
    }

    /*static int[] shiftLeft(int[] arr, int shift) {
      int[] tmp = new int[arr.length];
      System.arraycopy(arr, shift, tmp, 0, arr.length-shift);
      System.arraycopy(arr, 0, tmp, arr.length-shift, shift);
      return tmp;
    }*/

    static int[] shiftArray(int array[], int idx) {
      // get last index of array
      int lastIndex = array.length - 1; 
      // save first element
      //int oldFirst = array[0]; 
      int oldFirst = array[idx];

      // copy the elements from right to left
      for (int i = idx; i < lastIndex; i++) {
        array[i] = array[i + 1];
      }

      // put the first element last
      array[lastIndex] = oldFirst;

      return array;
    }

    static void fillPtable(int arr[]) {
      priorityTable = new HashMap<String, Integer>();
      for (int i = 0; i < arr.length; i++) {
        priorityTable.put("Test"+i, arr.length-i-1);
      }
      //System.out.println("PTABLE: " + priorityTable);
    }

    static class Priority<String> implements Comparator<String> {
      private String threadInfo;
      private int priorityNum;
      private HashMap<String, Integer> priorTable = new HashMap<String, Integer>();

      Priority(HashMap<String, Integer> pTable) {
        priorTable = pTable;
      }

      // Overriding compare method to sort by highest priority number
      public int compare(String t1, String t2) {
        //System.out.println("t1: " + t1 + "\t t2: " + t2);
        //System.out.println(priorTable.get(t1) + "\t" + priorTable.get(t2));
        return priorTable.get(t1) - priorTable.get(t2);
      }
    }

  }