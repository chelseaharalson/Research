import java.util.ArrayList;

/**
 *
 * @author chelseametcalf
 */
public class Node {
    Node parent;    // store parent node of current node to help in tracing path when answer is found
    ArrayList<String> solution;
    int numOfVars;
    int cohesion;
    
    int level;      // level of node in decision tree
    int profit;     // profit of nodes on path from root to this node (including this node)
    int bound;      // upper bound of max profit in subtree of this node
    
    public Node() {
        
    }
    
    /*public Node(ArrayList<String> pSolnSet) {
        this.solution = pSolnSet; 
    }*/
}
