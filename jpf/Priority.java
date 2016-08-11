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

class Priority implements Comparator<Priority>, Comparable<Priority> {
  // need to change String to ThreadInfo when implementing in listener
  private String threadInfo;
  private int priorityNum;
  Priority() {
  }

  Priority(String ti, int pNum) {
    threadInfo = ti;
    priorityNum = pNum;
  }

  public String getThreadInfo() {
    return threadInfo;
  }

  public int getPriorityNum() {
    return priorityNum;
  }

  // Overriding compareTo method
  public int compareTo(Priority p) {
    return (this.threadInfo).compareTo(p.threadInfo);
  }

  // Overriding compare method to sort priority number
  public int compare(Priority p1, Priority p2) {
    return p1.priorityNum - p2.priorityNum;
  }
}