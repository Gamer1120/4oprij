package clientserver;

import java.io.Serializable;

/**
 * Leaderboard class for the Connect4 according to the protocol of the TI-2
 * group.<br>
 * <br>
 * Programming Project Connect4 Module 2 Softwaresystems 2014-2015 <br>
 * 
 * @author Michael Koopman s1401335 and Sven Konings s1534130
 */
public class LeaderboardPair implements Comparable<LeaderboardPair>,
		Serializable {

	/**
	 * Auto generated serial UID for Serializable.
	 */
	private static final long serialVersionUID = 4797121270035180883L;
	/**
	 * The name belonging to this LeaderboardPair
	 */
	private String name;
	/**
	 * The score for this LeaderboardPair
	 */
	private int[] score;

	/**
	 * Creates a new LeaderboardPair object without any games played given a
	 * name.
	 * 
	 * @param name
	 *            The name for this Leaderboardpair.
	 */
	public LeaderboardPair(String name) {
		this(name, 0, 0, 0);
	}

	/**
	 * Creates a new LeaderboardPair given a name, the wins, losses and games
	 * played this person has.
	 * 
	 * @param name
	 *            The name for this LeaderboardPair.
	 * @param wins
	 *            The amount of wins this LeaderboardPair has.
	 * @param losses
	 *            The amount of losses this LeaderboardPair has.
	 * @param games
	 *            The amount of games this LeaderboardPair has played.
	 */
	public LeaderboardPair(String name, int wins, int losses, int games) {
		this.name = name;
		this.score = new int[] { wins, losses, games };
	}

	/**
	 * Returns the name for this LeaderboardPair.
	 * 
	 * @return The name for this LeaderboardPair.
	 */
	public String getName() {
		return name;
	}

	/**
	 * Returns the score this LeaderboardPair has.
	 * 
	 * @return The score this LeaderboardPair has.
	 */
	public int[] getScore() {
		return score;
	}

	/**
	 * Returns the amount of wins this LeaderboardPair has.
	 * 
	 * @return The amount of wins this LeaderboardPair has.
	 */
	public int getWins() {
		return score[0];
	}

	/**
	 * Returns the amount of losses this LeaderboardPair has.
	 * 
	 * @return The amount of losses this LeaderboardPair has.
	 */
	public int getLosses() {
		return score[1];
	}

	/**
	 * Returns the amount of games this LeaderboardPair has played.
	 * 
	 * @return The amount of games this LeaderboardPair has played.
	 */
	public int getGames() {
		return score[2];
	}

	/**
	 * Returns the amount of games this LeaderboardPair has played.
	 * 
	 * @return The amount of games this LeaderboardPair has played.
	 */
	public int getPoints() {
		return score[0] - score[1];
	}

	/**
	 * Updates this LeaderboardPair, adding a win and a game played.
	 */
	public void updateWin() {
		score[0]++;
		score[2]++;
	}

	/**
	 * Updates this LeaderboardPair, adding a loss and a game played.
	 */
	public void updateLoss() {
		score[1]++;
		score[2]++;
	}

	/**
	 * Updates this LeaderboardPair, adding a game played.
	 */
	public void updateDraw() {
		score[2]++;
	}

	/**
	 * Compares a LeaderboardPair to another one. This method is used to
	 * determine the order in which the Leaderboard needs to be given. First,
	 * the highest combined score is checked. If those are the same, the most
	 * wins are checked. If those are also the same, the least losses is
	 * checked. If that fails, the highest total games is checked. If that
	 * fails, it's sorted in alphabetical order (using it's name).
	 * 
	 * @param The
	 *            LeaderboardPair to compare this LeaderboardPair to.
	 * @return -1 if the LeaderboardPair is smaller than this, 1 if the
	 *         LeaderboardPair is bigger, 0 if they are the same.
	 */
	@Override
	public int compareTo(LeaderboardPair pair) {
		// Highest combined score
		if (this.getPoints() > pair.getPoints()) {
			return -1;
		} else if (this.getPoints() < pair.getPoints()) {
			return 1;
			// Most wins
		} else if (this.getWins() > pair.getWins()) {
			return -1;
		} else if (this.getWins() < pair.getWins()) {
			return 1;
			// Least losses
		} else if (this.getLosses() < pair.getLosses()) {
			return -1;
		} else if (this.getLosses() > pair.getLosses()) {
			return 1;
			// Highest total games
		} else if (this.getGames() > pair.getGames()) {
			return -1;
		} else if (this.getGames() < pair.getGames()) {
			return 1;
			// Alphabetical order (captital letters first)
		} else {
			return this.getName().compareTo(pair.getName());
		}
	}

	/**
	 * Checks if 2 LeaderboardPairs are the same.
	 * 
	 * @param o
	 *            The object to compare to this LeaderboardPair.
	 * @return Whether these two LeaderboardPairs are the same.
	 */
	@Override
	public boolean equals(Object o) {
		if (o instanceof LeaderboardPair) {
			return name.equals(((LeaderboardPair) o).getName())
					&& equalScore(o);
		} else {
			return false;
		}
	}

	/**
	 * Checks if 2 LeaderboardPairs have the same score.
	 * 
	 * @param o
	 *            The object to compare to this LeaderboardPair.
	 * @return Whether these two LeaderboardPairs have the same score.
	 */
	public boolean equalScore(Object o) {
		if (o instanceof LeaderboardPair) {
			LeaderboardPair pair = (LeaderboardPair) o;
			return this.getWins() == pair.getWins()
					&& this.getLosses() == pair.getLosses()
					&& this.getGames() == pair.getGames();
		} else {
			return false;
		}
	}

	/**
	 * Returns a String representation of this LeaderboardPair.
	 */
	@Override
	public String toString() {
		return getName() + " " + getWins() + " " + getLosses() + " "
				+ getGames();
	}
}
