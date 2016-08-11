import java.util.*;

public class PriorityExample {

  public static void main(String args[]) {
    //Priority pr = new Priority();

    // Takes a list of Priority objects
    List<Priority> pList = new ArrayList<Priority>();
    pList.add(new Priority("ThreadInfo4",4));
    pList.add(new Priority("ThreadInfo2",2));
    pList.add(new Priority("ThreadInfo5",5));
    pList.add(new Priority("ThreadInfo1",1));
    pList.add(new Priority("ThreadInfo3",3));

    // Printing sorted list of thread info
    for (Priority p : pList) {
      System.out.println(p.getThreadInfo() + ", ");
    }

    // Sorts the array list using comparator
    Collections.sort(pList, new Priority());
    System.out.println(" ");
    for (Priority pr : pList) {   // printing sorted list of priority numbers
      System.out.print(pr.getThreadInfo() + "  :  " + pr.getPriorityNum() + ", ");
    }

  }

}