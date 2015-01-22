package game;

import java.util.ArrayList;
import java.util.Random;
/**
 * NaiveStrategy for the Connect4 according to the protocol of the TI-2 group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class NaiveStrategy implements Strategy {
	public final static String NAME = "Naive";

	public String getName() {
		return NAME;
	}

	public int determineMove(Board b, Disc d) {
		ArrayList<Integer> empty = new ArrayList<Integer>();
		for (int col = 0; col < b.getColumns(); col++) {
			if (b.isEmptyField(col)) {
				empty.add(col);
			}
		}
		Random rng = new Random();
		return empty.get(rng.nextInt(empty.size()));
	}
}
