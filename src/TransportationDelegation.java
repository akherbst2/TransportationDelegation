import java.util.*;
import static java.lang.Math.*;
/**
 * Created by Alyssa on 10/8/2016.
 */
public class TransportationDelegation {
    static int s, r, f, t;
    public static void main(String[] args) {
        Scanner sc = new Scanner(System.in);
        s = Integer.parseInt(sc.next());
        r = Integer.parseInt(sc.next());
        f = Integer.parseInt(sc.next());
        t = Integer.parseInt(sc.next());
        HashMap<String, Node> map = new HashMap<>();
        HashSet<Node> rawMaterials = new HashSet<>();
        HashSet<Node> factories = new HashSet<>();
        MaxFlowSolver ff = new Dinic();
        Node src = ff.addNode();
        Node snk = ff.addNode();
        for(int i = 0; i < r; i++) {
            Node node = ff.addNode();
            ff.link(src, node, 1);
            String st = sc.next();
            node.name = st;
            map.put(st, node);
            rawMaterials.add(node);
        }
        for(int i = 0; i < f; i++) {
            Node node = ff.addNode();
            ff.link(node, snk, 1);
            String st = sc.next();
            node.name = st;
            map.put(st, node);
            factories.add(node);
        }
        //***************START WEIRD STUFF*********************************************************
        for(int i = 0; i < t; i++) {

            int n = Integer.parseInt(sc.next());
            Node prev = null;
            Node first = null;
            Node transportIn = ff.addNode();
            Node transportOut = ff.addNode();
            ff.link(transportIn, transportOut, 1);
            for(int j = 0; j < n; j++) {
                String s = sc.next();
                Node n1 = map.get(s);
                if(n1 == null) {
                    n1 = ff.addNode();
                    n1.name = s;
                    map.put(s, n1);
                }

                if(rawMaterials.contains(n1)) {
                    ff.link(n1, transportIn, 1);
                } else if(factories.contains(n1)) {
                    ff.link(transportOut, n1, 1);
                } else {    //intermediate
                    ff.link(transportOut, n1, 1);
                    ff.link(n1, transportIn, 1);
                }
            }

        }
        //***************END WEIRD STUFF***********************************************************
        System.out.print(ff.getMaxFlow(src, snk));

    }

    public static class Node {
        private Node() {}
        String name;
        List<Edge> edges = new ArrayList<>();
        int index;
    }

    public static class Edge {
        boolean forward;

        Node from, to;
        int flow;
        final int capacity;
        Edge dual;
        long cost;

        protected Edge(Node s, Node d, int c, boolean f) {
            forward = f;
            from = s;
            to = d;
            capacity = c;
        }

        int remaining() { return capacity - flow;  }

        void addFlow(int amount) {
            flow += amount;
            dual.flow -= amount;
        }
    }

    public static abstract class MaxFlowSolver {
        List<Node> nodes = new ArrayList<>();

        public void link(Node n1, Node n2, int capacity) {
            Edge e12 = new Edge(n1, n2, capacity, true);
            Edge e21 = new Edge(n2, n1, 0, false);
            e12.dual = e21;
            e21.dual = e12;
            n1.edges.add(e12);
            n2.edges.add(e21);
        }

        public void link(Node n1, Node n2, int capacity, long cost) {
            Edge e12 = new Edge(n1, n2, capacity, true);
            Edge e21 = new Edge(n2, n1, 0, false);
            e12.dual = e21;
            e21.dual = e12;
            n1.edges.add(e12);
            n2.edges.add(e21);
            e12.cost = cost;
            e21.cost = -cost;
        }

        public void link(int n1, int n2, int capacity){
            link(nodes.get(n1), nodes.get(n2), capacity);
        }

        protected MaxFlowSolver(int n) {
            for(int i = 0; i < n; i++) {
                addNode();
            }
        }

        protected MaxFlowSolver() {this(0);}

        public abstract int getMaxFlow(Node src, Node snk);

        public Node addNode() {
            Node n = new Node();
            n.index = nodes.size();
            nodes.add(n);
            return n;
        }
    }


    //HERE
    public static class Dinic extends MaxFlowSolver {
        int[ ]dist;
        boolean[] blocked;

        int BlockingFlow(Node src, Node snk) {
            int N = nodes.size();
            dist = new int[N];
            Arrays.fill(dist, -1);
            int[ ]Q = new int[N];
            int s = src.index;
            int t = snk.index;

            dist[s] = 0;
            int head = 0, tail = 0;
            Q[tail++] = s;
            while(head < tail) {
                int x = Q[head++];
                List<Edge> succ = nodes.get(x).edges;
                for(Edge e:succ) {
                    if(dist[e.to.index] == -1 && e.remaining() > 0) {
                        dist[e.to.index] = dist[e.from.index] + 1;
                        Q[tail++] = e.to.index;
                    }
                }
            }

            if(dist[t] == -1) {
                return 0;
            }

            int flow, totflow = 0;
            blocked = new boolean[N];
            do {
                flow = dfs(src, snk, Integer.MAX_VALUE);
                totflow += flow;
            } while (flow > 0);
            return totflow;
        }

        int dfs(Node v, Node snk, int mincap) {
            if(v == snk)
                return mincap;
            for(Edge e: v.edges) {
                if(!blocked[e.to.index]
                        &&dist[e.from.index] + 1 == dist[e.to.index]
                        && e.remaining() > 0) {
                    int flow = dfs(e.to, snk, min(mincap, e.remaining()));
                    if(flow > 0) {
                        e.addFlow(flow);
                        return flow;
                    }
                }
            }

            blocked[v.index] = true;
            return 0;
        }

        @Override
        public int getMaxFlow(Node src, Node snk) {
            int flow, totflow = 0;
            while ((flow = BlockingFlow(src, snk)) != 0)
                totflow += flow;
            return totflow;
        }

        public Dinic () { this(0); }
        public Dinic (int n) { super(n); }
    }


    static class FordFulkerson extends MaxFlowSolver {
        FordFulkerson() {this(0);}
        FordFulkerson(int n) { super(n);}


        @Override
        public int getMaxFlow(Node src, Node snk) {
            int total = 0;
            for(;;) {
                Edge[] prev = new Edge[nodes.size()];
                int addedFlow = findAugmentingPath(src, snk, prev);
                if(addedFlow == 0) break;
                total += addedFlow;

                for(Edge edge = prev[snk.index]; edge != null; edge = prev[edge.dual.to.index]) {
                    edge.addFlow(addedFlow);
                }
            }
            return total;
        }


        int findAugmentingPath(Node src, Node snk, Edge[] from) {
            Deque<Node> queue = new ArrayDeque<>();
            queue.offer(src);
            int N = nodes.size();
            int[] minCapacity = new int[N];
            boolean[] visited = new boolean[N];
            visited[src.index] = true;
            Arrays.fill(minCapacity, Integer.MAX_VALUE);
            while(queue.size() > 0) {
                Node node = queue.poll();
                if(node == snk)
                    return minCapacity[snk.index];
                for(Edge edge : node.edges) {
                    Node dest = edge.to;
                    if(edge.remaining() > 0 && !visited[dest.index]) {
                        visited[dest.index] = true;
                        from[dest.index] = edge;
                        minCapacity[dest.index] = min(minCapacity[node.index],
                                                      edge.remaining());
                        if(dest == snk)
                            return minCapacity[snk.index];
                        queue.push(dest);
                    }
                }
            }
            return 0;
        }

    }

}
