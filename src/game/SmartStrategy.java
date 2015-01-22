package game;

import java.util.Random;
import java.util.ArrayList;

public class SmartStrategy implements Strategy {
	public final static String NAME = "Smart";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		ArrayList<Integer> empty = new ArrayList<Integer>();
		for (int i = 0; i < b.getColumns(); i++) {
			if (b.isEmptyField(i)) {
				empty.add(i);
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d);
			if (board.gameOver()) {
				return i;
			}
		}
		for (Integer i : empty) {
			Board board = b.deepCopy();
			board.insertDisc(i, d.other());
			if (board.gameOver()) {
				return i;
			}
		}
		Random rng = new Random();
		return empty.get(rng.nextInt(empty.size()));
	}
}
