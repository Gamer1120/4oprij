package game;
public class MinMaxStrategy implements Strategy {
	public final static String NAME = "MinMax";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		Minimax strategy = new Minimax(b, 12);
		return strategy.alphaBeta(d);
	}
}
