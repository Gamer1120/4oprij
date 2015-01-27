package temp;

import game.Board;
import game.Disc;
import game.Strategy;

public class MinMaxStrategy implements Strategy {
	public final static String NAME = "MinMax";

	@Override
	public String getName() {
		return NAME;
	}

	@Override
	public int determineMove(Board b, Disc d) {
		Minimax strategy = new Minimax(b, 8);
		return strategy.alphaBeta(d);
	}
}
