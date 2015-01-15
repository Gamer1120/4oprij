package clientserver;

import game.Board;

import java.io.IOException;
import java.net.ServerSocket;
import java.net.Socket;
import java.util.ArrayList;
import java.util.ListIterator;

/**
 * P2 prac wk5. <br>
 * Server. A Thread class that listens to a socket connection on a specified
 * port. For every socket connection with a Client, a new ClientHandler thread
 * is started.
 * 
 * @author Theo Ruys
 * @version 2005.02.21
 */
public class Server extends Thread {
	// PROTOCOL
	public static final String ACCEPT_CONNECT = "OK";
	public static final String ERROR = "ERROR";
	public static final String LOBBY = "LOBBY";
	public static final String INVITE = "INVITE";
	public static final String GAME_START = "START";
	public static final String GAME_END = "END";
	public static final String REQUEST_MOVE = "REQUEST";
	public static final String MOVE_OK = "MOVE";
	public static final String BOARD = "BOARD";
	public static final String CHAT = "CHAT";
	public static final String LEADERBOARD = "LEADERBOARD";
	// END OF PROTOCOL
	private int port;
	private MessageUI mui;
	private ArrayList<ClientHandler> threads;
	private ArrayList<String[]> invites;

	/** Constructs a new Server object */
	public Server(int portArg, MessageUI muiArg) {
		this.port = portArg;
		this.mui = muiArg;
		this.threads = new ArrayList<ClientHandler>();
		this.invites = new ArrayList<String[]>();
	}

	/**
	 * Listens to a port of this Server if there are any Clients that would like
	 * to connect. For every new socket connection a new ClientHandler thread is
	 * started that takes care of the further communication with the Client.
	 */
	public void run() {
		try {
			ServerSocket ss = new ServerSocket(port);
			while (true) {
				Socket s = ss.accept();
				ClientHandler ch = new ClientHandler(this, s);
				addHandler(ch);
				ch.start();
			}
		} catch (IOException e) {
			//TODO: betere error handling?
			e.printStackTrace();

		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients.
	 * 
	 * @param msg
	 *            message that is send
	 */
	public void broadcast(String msg) {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				ch.sendMessage(msg);
			}
			mui.addMessage("Server: " + msg);
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to all
	 * connected Clients without a game.
	 * 
	 * @param msg
	 *            message that is send
	 */
	public void broadcastLobby() {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (!ch.inGame()) {
					ch.sendMessage(LOBBY + getLobby());
				}
			}
			mui.addMessage("Lobby:" + getLobby());
		}
	}

	/**
	 * Sends a message using the collection of connected ClientHandlers to the
	 * Client with the specified name
	 * 
	 * @param name
	 *            name of the client
	 * @param msg
	 *            message that is send
	 */
	public void sendMessage(String name, String msg) {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (ch.getClientName().equals(name)) {
					ch.sendMessage(msg);
					break;
				}
			}
			mui.addMessage("Server to " + name + ": " + msg);
		}
	}

	/**
	 * Checks wether the client with the specified name is in a game
	 * 
	 * @param name
	 *            name of the client
	 * @param board
	 *            board that is send
	 */
	public boolean inGame(String name) {
		synchronized (threads) {
			boolean game = false;
			for (ClientHandler ch : threads) {
				if (ch.getClientName().equals(name) && ch.inGame()) {
					game = true;
					break;
				}
			}
			return game;
		}
	}

	/**
	 * Sends the board to use for the game so both clientHandlers are using the
	 * same board
	 * 
	 * @param name
	 *            name of the client
	 * @param board
	 *            board that is send
	 */
	public void startGame(String name, Board board) {
		synchronized (threads) {
			for (ClientHandler ch : threads) {
				if (ch.getClientName().equals(name)) {
					ch.setBoard(board);
					break;
				}
			}
			mui.addMessage("Server: Set board for " + name);
		}
	}

	/**
	 * Print the message on the server gui
	 * 
	 * @param msg
	 *            message that is send
	 */
	public void print(String msg) {
		mui.addMessage("ClientHandler" + msg);
	}

	/**
	 * Checks if the name isn't already in use
	 */
	public boolean nameExists(String name) {
		synchronized (threads) {
			boolean available = false;
			for (ClientHandler ch : threads) {
				if (name.equals(ch.getClientName())) {
					available = true;
					break;
				}
			}
			return available;
		}
	}

	/**
	 * Sends an string with the connected client names that aren't playing a
	 * game
	 */
	public String getLobby() {
		synchronized (threads) {
			String clients = "";
			for (ClientHandler ch : threads) {
				if (!ch.inGame()) {
					clients += " " + ch.getClientName();
				}
			}
			return clients;
		}
	}

	/**
	 * Add a ClientHandler to the collection of ClientHandlers.
	 * 
	 * @param handler
	 *            ClientHandler that will be added
	 */
	public void addHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.add(handler);
		}
	}

	/**
	 * Remove a ClientHandler from the collection of ClientHanlders.
	 * 
	 * @param handler
	 *            ClientHandler that will be removed
	 */
	public void removeHandler(ClientHandler handler) {
		synchronized (threads) {
			threads.remove(handler);
		}
	}

	/**
	 * Add the names of the inviting and the invited client in a list
	 * 
	 * @param name
	 *            name of the inviting client
	 * @param invited
	 *            name of the invited client
	 */
	public void addInvite(String name, String invited) {
		synchronized (invites) {
			invites.add(new String[] { name, invited });
		}
	}

	/**
	 * Checks wether the client is invited by the client with the specified name
	 * 
	 * @param name
	 *            the name of the client that send the invite
	 * @param invited
	 *            the name of the client that received the invite
	 */
	public boolean isInvited(String name, String invited) {
		synchronized (invites) {
			boolean retBool = false;
			for (String[] invite : invites) {
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					retBool = true;
					break;
				}
			}
			return retBool;
		}
	}

	/**
	 * Removes the invite of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 * @param invited
	 *            the name of the invited client
	 */
	public void removeInvite(String name, String invited) {
		synchronized (invites) {
			for (ListIterator<String[]> iter = invites.listIterator(); iter
					.hasNext();) {
				String[] invite = iter.next();
				if (invite[0].equals(name) && invite[1].equals(invited)) {
					iter.remove();
					break;
				}
			}
		}
	}

	/**
	 * Removes all invites of the client with the specified name.
	 * 
	 * @param name
	 *            the name of the client
	 */
	public void removeAllInvites(String name) {
		synchronized (invites) {
			for (ListIterator<String[]> iter = invites.listIterator(); iter
					.hasNext();) {
				String[] invite = iter.next();
				if (invite[0].equals(name) || invite[1].equals(name)) {
					iter.remove();
				}
			}
		}
	}
} // end of class Server
