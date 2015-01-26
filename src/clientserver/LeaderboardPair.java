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
	private String name;
	private int[] score;

	public LeaderboardPair(String name) {
		this(name, 0, 0, 0);
	}

	public LeaderboardPair(String name, int wins, int losses, int games) {
		this.name = name;
		this.score = new int[] { wins, losses, games };
	}

	public String getName() {
		return name;
	}

	public int[] getScore() {
		return score;
	}

	public int getWins() {
		return score[0];
	}

	public int getLosses() {
		return score[1];
	}

	public int getGames() {
		return score[2];
	}

	public int getPoints() {
		return score[0] - score[1];
	}

	public void updateWin() {
		score[0]++;
		score[2]++;
	}

	public void updateLoss() {
		score[1]++;
		score[2]++;
	}

	public void updateDraw() {
		score[2]++;
	}

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

	public boolean equals(Object o) {
		if (o instanceof LeaderboardPair) {
			return name.equals(((LeaderboardPair) o).getName())
					&& equalScore(o);
		} else {
			return false;
		}
	}

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

	public String toString() {
		return getName() + " " + getWins() + " " + getLosses() + " "
				+ getGames();
	}
}
