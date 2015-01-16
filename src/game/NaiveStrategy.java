package game;

import java.util.HashSet;
import java.util.Set;

public class NaiveStrategy implements Strategy {
	public final static String NAME = "Naive";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		Set<Integer> empty = new HashSet<Integer>();
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				empty.add(col);
			}
		}
		return (int) empty.toArray()[((int) (Math.random() * empty.size()))];
	}
}
